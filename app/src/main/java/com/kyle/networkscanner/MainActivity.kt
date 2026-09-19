package com.kyle.networkscanner

import android.app.NotificationChannel
import android.app.NotificationManager
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.content.res.ColorStateList
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.RectF
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.net.ConnectivityManager
import android.net.Network
import android.net.NetworkCapabilities
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.system.ErrnoException
import android.system.OsConstants
import android.text.InputType
import android.view.Gravity
import android.view.View
import android.view.ViewGroup
import android.widget.*
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import androidx.core.app.NotificationCompat
import androidx.core.app.NotificationManagerCompat
import androidx.core.content.ContextCompat
import java.io.File
import java.net.*
import java.text.SimpleDateFormat
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicLong

data class NetworkDevice(
    val ipAddress: String,
    var deviceName: String,
    var hostname: String,
    var macAddress: String,
    var deviceType: String,
    var isThisDevice: Boolean,
    var openPorts: MutableList<Int>,
    var portsChecked: Boolean = false,
    var isNewDevice: Boolean = false,
    var firstSeen: Long = 0L,
    var lastSeen: Long = 0L
)

private data class KnownDevice(
    val ipAddress: String,
    var hostname: String,
    var macAddress: String,
    var deviceType: String,
    var firstSeen: Long,
    var lastSeen: Long
)

private data class Ipv4Subnet(val local: Long, val prefix: Int) {
    val mask = (0xFFFFFFFFL shl (32 - prefix)) and 0xFFFFFFFFL
    val network = local and mask
    val broadcast = network or (mask xor 0xFFFFFFFFL)
    val first = if (prefix >= 31) network else network + 1
    val last = if (prefix >= 31) broadcast else broadcast - 1
    val hostCount = last - first + 1
    val cidr get() = "${ipv4Text(network)}/$prefix"
}

private fun ipv4Number(address: Inet4Address): Long {
    var value = 0L
    for (b in address.address) value = (value shl 8) or (b.toLong() and 255)
    return value
}

private fun ipv4Text(v: Long) =
    "${(v shr 24) and 255}.${(v shr 16) and 255}.${(v shr 8) and 255}.${v and 255}"

private fun parseIpv4(text: String): Long? {
    val p = text.trim().split(".")
    if (p.size != 4) return null
    var result = 0L

    for (part in p) {
        val n = part.toIntOrNull() ?: return null
        if (n !in 0..255) return null
        result = (result shl 8) or n.toLong()
    }

    return result
}

class MainActivity : AppCompatActivity() {

    private lateinit var txtIpAddress: TextView
    private lateinit var txtSubnet: TextView
    private lateinit var txtStatus: TextView
    private lateinit var txtDevicesFound: TextView
    private lateinit var txtPortCount: TextView
    private lateinit var txtCheckedCount: TextView
    private lateinit var txtPhase: TextView
    private lateinit var txtTransport: TextView
    private lateinit var txtResultNote: TextView
    private lateinit var btnScan: Button
    private lateinit var progressScan: ProgressBar
    private lateinit var deviceContainer: LinearLayout
    private lateinit var emptyState: LinearLayout
    private lateinit var connectivity: ConnectivityManager
    private lateinit var radar: RadarView
    private lateinit var preferences: SharedPreferences

    private val ink = Color.rgb(8, 13, 18)
    private val panel = Color.rgb(17, 25, 33)
    private val border = Color.rgb(38, 54, 64)
    private val lime = Color.rgb(190, 255, 89)
    private val cyan = Color.rgb(88, 222, 235)
    private val primaryText = Color.rgb(235, 243, 246)
    private val mutedText = Color.rgb(151, 171, 183)
    private val alertColor = Color.rgb(255, 190, 80)

    private val ui = Handler(Looper.getMainLooper())
    private val devices = LinkedHashMap<String, NetworkDevice>()
    private val cards = HashMap<String, View>()
    private val knownDevices = LinkedHashMap<String, KnownDevice>()
    private val notifiedThisScan = HashSet<String>()

    private var checkedHosts = 0
    private var totalHosts = 0
    private var selectedLan: Lan? = null
    private var session: ScanSession? = null
    private var destroyed = false
    private var inputDialog: AlertDialog? = null
    private var baselineEstablished = false

    companion object {
        private const val WORKERS = 40
        private const val MAX_HOSTS_PER_SCAN = 4096L
        private const val CONNECT_TIMEOUT_MS = 250
        private const val PREFS_NAME = "net_scanner_devices"
        private const val PREF_BASELINE = "baseline_established"
        private const val PREF_DEVICE_SET = "known_devices"
        private const val CHANNEL_ID = "new_device_alerts"
        private const val CHANNEL_NAME = "New Device Alerts"
        private const val NOTIFICATION_REQUEST = 1001
        private const val POST_NOTIFICATIONS_PERMISSION = "android.permission.POST_NOTIFICATIONS"

        private val PORTS = intArrayOf(
            22, 53, 80, 139, 443, 445, 554, 631,
            8008, 8009, 8080, 9100
        )
    }

    private data class Lan(
        val network: Network,
        val ip: String,
        val interfaceName: String,
        val transport: String,
        val subnet: Ipv4Subnet
    )

    private class ScanSession(val lan: Lan, val first: Long, val last: Long) {
        val nextAddress = AtomicLong(first)
        val total = (last - first + 1).toInt()
        val executor = Executors.newFixedThreadPool(minOf(WORKERS, total))
        val sockets = ConcurrentHashMap<Socket, Boolean>()

        @Volatile var cancelled = false
        var completed = 0

        fun stop() {
            cancelled = true
            sockets.keys.forEach {
                try { it.close() } catch (_: Exception) {}
            }
            executor.shutdownNow()
        }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        setTheme(androidx.appcompat.R.style.Theme_AppCompat_NoActionBar)
        super.onCreate(savedInstanceState)

        buildDashboard()

        connectivity = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
        preferences = getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
        baselineEstablished = preferences.getBoolean(PREF_BASELINE, false)

        loadKnownDevices()
        createNotificationChannel()
        requestNotificationPermission()

        btnScan.setOnClickListener {
            if (session != null) stopScan("Scan cancelled") else chooseNetwork()
        }
    }

    // ==================== KNOWN DEVICES ====================

    private fun loadKnownDevices() {
        knownDevices.clear()

        preferences.getStringSet(PREF_DEVICE_SET, emptySet())?.forEach {
            try {
                val p = it.split("|")
                if (p.size < 6) return@forEach

                val first = p[4].toLongOrNull() ?: return@forEach
                val last = p[5].toLongOrNull() ?: first

                knownDevices[p[0]] =
                    KnownDevice(p[0], p[1], p[2], p[3], first, last)
            } catch (_: Exception) {}
        }
    }

    private fun saveKnownDevices() {
        val set = knownDevices.values.map {
            "${it.ipAddress}|${it.hostname.replace("|", " ")}|" +
                "${it.macAddress.replace("|", " ")}|" +
                "${it.deviceType.replace("|", " ")}|${it.firstSeen}|${it.lastSeen}"
        }.toSet()

        preferences.edit().putStringSet(PREF_DEVICE_SET, set).apply()
    }

    private fun registerDevice(d: NetworkDevice) {
        val now = System.currentTimeMillis()
        val old = knownDevices[d.ipAddress]

        if (old != null) {
            d.isNewDevice = false
            d.firstSeen = old.firstSeen
            d.lastSeen = now
            old.hostname = d.hostname
            old.macAddress = d.macAddress
            old.deviceType = d.deviceType
            old.lastSeen = now
        } else {
            d.firstSeen = now
            d.lastSeen = now
            d.isNewDevice = baselineEstablished && !d.isThisDevice

            knownDevices[d.ipAddress] = KnownDevice(
                d.ipAddress, d.hostname, d.macAddress,
                d.deviceType, now, now
            )

            if (d.isNewDevice && notifiedThisScan.add(d.ipAddress))
                showNewDeviceNotification(d)
        }

        if (d.isThisDevice) d.isNewDevice = false
        saveKnownDevices()
    }

    // ==================== NOTIFICATIONS ====================

    private fun createNotificationChannel() {
        if (Build.VERSION.SDK_INT < 26) return

        val channel = NotificationChannel(
            CHANNEL_ID,
            CHANNEL_NAME,
            NotificationManager.IMPORTANCE_HIGH
        ).apply {
            description = "Alerts when a new device appears on the local network"
            enableVibration(true)
        }

        (getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager)
            .createNotificationChannel(channel)
    }

    private fun requestNotificationPermission() {
        if (
            Build.VERSION.SDK_INT >= 33 &&
            ContextCompat.checkSelfPermission(
                this,
                POST_NOTIFICATIONS_PERMISSION
            ) != PackageManager.PERMISSION_GRANTED
        ) {
            requestPermissions(
                arrayOf(POST_NOTIFICATIONS_PERMISSION),
                NOTIFICATION_REQUEST
            )
        }
    }

    private fun showNewDeviceNotification(d: NetworkDevice) {
        if (
            Build.VERSION.SDK_INT >= 33 &&
            ContextCompat.checkSelfPermission(
                this,
                POST_NOTIFICATIONS_PERMISSION
            ) != PackageManager.PERMISSION_GRANTED
        ) return

        val notification = NotificationCompat.Builder(this, CHANNEL_ID)
            .setSmallIcon(android.R.drawable.stat_notify_sync)
            .setContentTitle("New device detected")
            .setContentText("${d.ipAddress} · ${d.deviceType}")
            .setStyle(
                NotificationCompat.BigTextStyle().bigText(
                    "A previously unseen device responded on your network.\n\n" +
                        "IP: ${d.ipAddress}\n" +
                        "Device: ${d.hostname}\n" +
                        "Type: ${d.deviceType}"
                )
            )
            .setPriority(NotificationCompat.PRIORITY_HIGH)
            .setAutoCancel(true)
            .build()

        try {
            NotificationManagerCompat.from(this)
                .notify(d.ipAddress.hashCode() and 0x7FFFFFFF, notification)
        } catch (_: SecurityException) {}
    }

    // ==================== UI HELPERS ====================

    private fun dp(v: Int) = (v * resources.displayMetrics.density + .5f).toInt()

    private fun surface(
        fill: Int = panel,
        stroke: Int = border,
        radius: Int = 20
    ) = GradientDrawable().apply {
        setColor(fill)
        cornerRadius = dp(radius).toFloat()
        setStroke(dp(1), stroke)
    }

    private fun label(
        textValue: String,
        size: Float = 14f,
        color: Int = primaryText,
        mono: Boolean = false,
        bold: Boolean = false
    ) = TextView(this).apply {
        text = textValue
        textSize = size
        setTextColor(color)
        typeface = Typeface.create(
            if (mono) "monospace" else "sans-serif",
            if (bold) Typeface.BOLD else Typeface.NORMAL
        )
        includeFontPadding = false
    }

    private fun column() = LinearLayout(this).apply {
        orientation = LinearLayout.VERTICAL
    }

    private fun row() = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL
        gravity = Gravity.CENTER_VERTICAL
    }

    private fun addBlock(parent: LinearLayout, view: View, gap: Int = 12) {
        parent.addView(
            view,
            LinearLayout.LayoutParams(-1, -2).apply { topMargin = dp(gap) }
        )
    }

    private fun badge(text: String, color: Int = cyan) =
        label(text, 11f, color, true, true).apply {
            background = surface(panel, border, 8)
            setPadding(dp(10), dp(7), dp(10), dp(7))
        }

    private fun action(text: String, filled: Boolean = false) =
        Button(this).apply {
            this.text = text
            textSize = 13f
            isAllCaps = false
            typeface = Typeface.create("monospace", Typeface.BOLD)
            setTextColor(if (filled) ink else cyan)
            minHeight = dp(50)
            minimumHeight = dp(50)
            backgroundTintList = null
            background = RippleDrawable(
                ColorStateList.valueOf(0x3368DDEB),
                surface(
                    if (filled) lime else panel,
                    if (filled) lime else border,
                    12
                ),
                null
            )
            stateListAnimator = null
        }

    private fun metric(
        parent: LinearLayout,
        title: String,
        color: Int,
        gap: Boolean
    ): TextView {
        val box = column().apply {
            background = surface()
            setPadding(dp(12), dp(16), dp(8), dp(16))
        }

        val value = label("0", 26f, color, true, true)
        box.addView(value)
        addBlock(box, label(title, 10f, mutedText, true), 8)

        parent.addView(
            box,
            LinearLayout.LayoutParams(0, -1, 1f).apply {
                if (gap) marginStart = dp(8)
            }
        )

        return value
    }

    // ==================== DASHBOARD ====================

    @Suppress("DEPRECATION")
    private fun buildDashboard() {
        window.statusBarColor = ink
        window.navigationBarColor = ink

        val root = column().apply {
            setBackgroundColor(ink)
            fitsSystemWindows = true
        }

        val scroll = ScrollView(this).apply {
            isFillViewport = true
            isVerticalScrollBarEnabled = false
        }

        val content = column().apply {
            setPadding(dp(20), dp(24), dp(20), dp(28))
        }

        scroll.addView(content)
        root.addView(scroll, LinearLayout.LayoutParams(-1, -1))
        setContentView(root)

        val header = row()
        header.addView(label("[ N ]", 23f, lime, true, true))

        val brand = column().apply { setPadding(dp(12), 0, 0, 0) }
        brand.addView(label("NET / SCANNER", 17f, primaryText, false, true))
        addBlock(brand, label("LOCAL NETWORK CONSOLE", 10f, mutedText, true), 5)
        header.addView(brand)

        content.addView(header)
        addBlock(content, label("Network overview", 28f, primaryText, false, true), 28)
        addBlock(
            content,
            label("Discover devices. Inspect services. Detect changes.", 14f, mutedText),
            8
        )

        val hero = column().apply {
            background = surface()
            setPadding(dp(18), dp(18), dp(18), dp(18))
        }

        val heroTop = row()
        txtPhase = label("●  STANDBY", 12f, lime, true, true)
        heroTop.addView(txtPhase, LinearLayout.LayoutParams(0, -2, 1f))

        txtTransport = badge("NO LINK")
        heroTop.addView(txtTransport)
        hero.addView(heroTop)

        radar = RadarView(this)
        hero.addView(radar, LinearLayout.LayoutParams(-1, dp(154)))

        txtIpAddress = label("No local IPv4", 22f, primaryText, true, true)
        addBlock(hero, label("LOCAL ADDRESS", 10f, mutedText, true), 4)
        addBlock(hero, txtIpAddress, 8)

        txtSubnet = label("Connect to Wi-Fi or Ethernet", 12f, mutedText, true)
        addBlock(hero, txtSubnet, 10)
        addBlock(content, hero, 24)

        val metrics = row()
        txtDevicesFound = metric(metrics, "DEVICES", lime, false)
        txtPortCount = metric(metrics, "OPEN PORTS", cyan, true)
        txtCheckedCount = metric(metrics, "CHECKED", primaryText, true)
        addBlock(content, metrics, 12)

        val scanPanel = column().apply {
            background = surface()
            setPadding(dp(16), dp(16), dp(16), dp(16))
        }

        scanPanel.addView(label(">_ SCAN SESSION", 11f, cyan, true, true))

        txtStatus = label("Waiting for a local network", 13f, primaryText, true)
        addBlock(scanPanel, txtStatus, 12)

        progressScan = ProgressBar(
            this, null, android.R.attr.progressBarStyleHorizontal
        ).apply {
            progressTintList = ColorStateList.valueOf(lime)
            progressBackgroundTintList = ColorStateList.valueOf(border)
            visibility = View.GONE
        }

        scanPanel.addView(
            progressScan,
            LinearLayout.LayoutParams(-1, dp(8)).apply { topMargin = dp(12) }
        )

        btnScan = action("Start scan  →", true)
        addBlock(scanPanel, btnScan, 16)
        addBlock(content, scanPanel, 12)

        addBlock(
            content,
            label("Discovered devices", 20f, primaryText, false, true),
            26
        )

        txtResultNote = label(
            "Run a scan to discover your local network.",
            12f,
            mutedText
        )
        addBlock(content, txtResultNote, 6)

        emptyState = column().apply {
            background = surface()
            gravity = Gravity.CENTER
            setPadding(dp(24), dp(28), dp(24), dp(28))
        }

        emptyState.addView(label("[  ·  ·  ·  ]", 24f, cyan, true))

        addBlock(
            emptyState,
            label("Your network, mapped here", 16f, primaryText, false, true),
            16
        )

        addBlock(
            emptyState,
            label("Start a scan to see device addresses and services.", 13f, mutedText),
            8
        )

        addBlock(content, emptyState, 14)

        deviceContainer = column()
        addBlock(content, deviceContainer, 2)

        addBlock(
            content,
            label(
                "NEW = first detected after your baseline scan.\n" +
                    "KNOWN = previously observed device.\n" +
                    "Web interfaces can be opened from Inspect Device.",
                11f,
                mutedText
            ),
            20
        )
    }

    private fun updateMetrics() {
        txtDevicesFound.text = devices.size.toString()

        var ports = 0
        devices.values.forEach { ports += it.openPorts.size }

        txtPortCount.text = ports.toString()
        txtCheckedCount.text = checkedHosts.toString()
        emptyState.visibility = if (devices.isEmpty()) View.VISIBLE else View.GONE
    }

    private fun setScanAppearance(scanning: Boolean, phase: String) {
        txtPhase.text = "●  $phase"
        txtPhase.setTextColor(if (scanning) lime else cyan)
        radar.setScanning(scanning)
        btnScan.setTextColor(if (scanning) primaryText else ink)

        btnScan.background = RippleDrawable(
            ColorStateList.valueOf(0x3368DDEB),
            surface(
                if (scanning) panel else lime,
                if (scanning) cyan else lime,
                12
            ),
            null
        )
    }

    // ==================== RADAR ====================

    private inner class RadarView(context: Context) : View(context) {
        private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
        private val bounds = RectF()
        private var scanning = false

        fun setScanning(value: Boolean) {
            scanning = value
            invalidate()
        }

        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)

            val cx = width / 2f
            val cy = height / 2f
            val radius = minOf(width, height) * .42f

            paint.style = Paint.Style.STROKE
            paint.strokeWidth = resources.displayMetrics.density
            paint.color = border

            for (i in 1..3)
                canvas.drawCircle(cx, cy, radius * i / 3f, paint)

            canvas.drawLine(cx - radius, cy, cx + radius, cy, paint)
            canvas.drawLine(cx, cy - radius, cx, cy + radius, paint)

            bounds.set(cx - radius, cy - radius, cx + radius, cy + radius)

            val angle =
                if (scanning)
                    (SystemClock.uptimeMillis() % 2800) * 360f / 2800
                else -45f

            paint.color = cyan
            paint.strokeWidth = dp(2).toFloat()
            canvas.drawArc(bounds, angle - 65, 65f, false, paint)

            if (scanning) {
                paint.style = Paint.Style.FILL
                paint.color = 0x163ADDCD
                canvas.drawArc(bounds, angle - 65, 65f, true, paint)
            }

            paint.style = Paint.Style.FILL
            paint.color = lime
            canvas.drawCircle(cx, cy, dp(4).toFloat(), paint)

            if (scanning && isShown) postInvalidateOnAnimation()
        }
    }

    // ==================== NETWORK ====================

    override fun onResume() {
        super.onResume()
        if (session == null) refreshNetwork()
    }

    private fun isLan(c: NetworkCapabilities) =
        !c.hasTransport(NetworkCapabilities.TRANSPORT_VPN) &&
            c.hasCapability(NetworkCapabilities.NET_CAPABILITY_NOT_VPN) &&
            (
                c.hasTransport(NetworkCapabilities.TRANSPORT_WIFI) ||
                    c.hasTransport(NetworkCapabilities.TRANSPORT_ETHERNET)
                )

    @Suppress("DEPRECATION")
    private fun availableLans(): List<Lan> {
        val result = arrayListOf<Lan>()

        connectivity.allNetworks.forEach { network ->
            val caps = connectivity.getNetworkCapabilities(network) ?: return@forEach
            if (!isLan(caps)) return@forEach

            val links = connectivity.getLinkProperties(network) ?: return@forEach
            val iface = links.interfaceName ?: return@forEach

            val transport =
                if (caps.hasTransport(NetworkCapabilities.TRANSPORT_WIFI))
                    "Wi-Fi"
                else "Ethernet"

            links.linkAddresses.forEach { link ->
                val address = link.address as? Inet4Address ?: return@forEach

                if (
                    address.isLoopbackAddress ||
                    address.isAnyLocalAddress ||
                    address.isMulticastAddress
                ) return@forEach

                val ip = address.hostAddress ?: return@forEach

                result += Lan(
                    network,
                    ip,
                    iface,
                    transport,
                    Ipv4Subnet(ipv4Number(address), link.prefixLength)
                )
            }
        }

        return result
    }

    private fun refreshNetwork(): List<Lan> {
        val lans = try { availableLans() } catch (_: Exception) { emptyList() }
        selectedLan = lans.firstOrNull()

        if (selectedLan == null) {
            txtIpAddress.text = "No local IPv4"
            txtTransport.text = "NO LINK"
            txtSubnet.text = "Subnet: Not detected"
            txtStatus.text = "Connect to Wi-Fi or Ethernet"
            btnScan.text = "Retry"
            setScanAppearance(false, "OFFLINE")
        } else {
            showNetwork(selectedLan!!)
            txtStatus.text = "Ready to scan ${selectedLan!!.transport}"
            btnScan.text = "Start scan  →"
            setScanAppearance(false, "READY")
        }

        return lans
    }

    private fun showNetwork(lan: Lan) {
        txtIpAddress.text = lan.ip
        txtTransport.text = lan.transport.toUpperCase(Locale.ROOT)
        txtSubnet.text = "${lan.subnet.cidr}\nMask: ${ipv4Text(lan.subnet.mask)}"
    }

    private fun chooseNetwork() {
        val lans = refreshNetwork()
        if (lans.isEmpty()) return

        if (lans.size == 1) {
            chooseRange(lans[0])
            return
        }

        val labels = lans.map {
            "${it.transport} (${it.interfaceName})\n${it.ip} - ${it.subnet.cidr}"
        }.toTypedArray()

        AlertDialog.Builder(this)
            .setTitle("Choose a local network")
            .setItems(labels) { _, i -> chooseRange(lans[i]) }
            .setNegativeButton("Cancel", null)
            .show()
    }

    private fun chooseRange(lan: Lan) {
        selectedLan = lan

        if (lan.subnet.hostCount <= MAX_HOSTS_PER_SCAN) {
            startScan(lan, lan.subnet.first, lan.subnet.last)
            return
        }

        val block = lan.subnet.local and 0xFFFFFF00L
        val first = maxOf(lan.subnet.first, block)
        val last = minOf(lan.subnet.last, block + 255)

        val layout = column().apply {
            setPadding(dp(20), 0, dp(20), 0)
        }

        val from = EditText(this).apply {
            hint = "First IPv4 address"
            inputType = InputType.TYPE_CLASS_TEXT
            setText(ipv4Text(first))
        }

        val to = EditText(this).apply {
            hint = "Last IPv4 address"
            inputType = InputType.TYPE_CLASS_TEXT
            setText(ipv4Text(last))
        }

        layout.addView(from)
        layout.addView(to)

        val dialog = AlertDialog.Builder(this)
            .setTitle("Choose scan range")
            .setView(layout)
            .setPositiveButton("Scan", null)
            .setNegativeButton("Cancel", null)
            .create()

        dialog.setOnShowListener {
            dialog.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener {
                val start = parseIpv4(from.text.toString())
                val end = parseIpv4(to.text.toString())

                when {
                    start == null || start !in lan.subnet.first..lan.subnet.last ->
                        from.error = "Invalid address"

                    end == null || end !in lan.subnet.first..lan.subnet.last ->
                        to.error = "Invalid address"

                    end < start ->
                        to.error = "Must be after first address"

                    end - start + 1 > MAX_HOSTS_PER_SCAN ->
                        to.error = "Maximum $MAX_HOSTS_PER_SCAN addresses"

                    else -> {
                        dialog.dismiss()
                        startScan(lan, start, end)
                    }
                }
            }
        }

        dialog.show()
    }

    private fun isStillConnected(lan: Lan): Boolean = try {
        val caps = connectivity.getNetworkCapabilities(lan.network)
        val links = connectivity.getLinkProperties(lan.network)

        caps != null &&
            isLan(caps) &&
            links?.interfaceName == lan.interfaceName
    } catch (_: Exception) {
        false
    }

    // ==================== SCAN ====================

    private fun startScan(lan: Lan, first: Long, last: Long) {
        if (!isStillConnected(lan)) {
            refreshNetwork()
            return
        }

        val scan = ScanSession(lan, first, last)
        session = scan

        devices.clear()
        cards.clear()
        notifiedThisScan.clear()
        deviceContainer.removeAllViews()

        checkedHosts = 0
        totalHosts = scan.total
        updateMetrics()

        setScanAppearance(true, "SCANNING")

        txtResultNote.text =
            if (baselineEstablished)
                "Current scan · watching for new devices"
            else
                "First scan · establishing device baseline"

        progressScan.max = scan.total
        progressScan.progress = 0
        progressScan.visibility = View.VISIBLE

        btnScan.text = "Stop scan  ■"
        txtStatus.text = "Scanning... 0 / ${scan.total}"

        val phone = localDeviceName()

        val own = NetworkDevice(
            lan.ip,
            "$phone (This device)",
            phone,
            getMacAddress(lan.ip, lan.interfaceName),
            "Android Phone / Tablet",
            true,
            mutableListOf()
        )

        registerDevice(own)
        displayDevice(own)

        repeat(minOf(WORKERS, scan.total)) {
            scan.executor.execute {
                while (!scan.cancelled && !Thread.currentThread().isInterrupted) {
                    val address = scan.nextAddress.getAndIncrement()
                    if (address > scan.last) break

                    val result = scanHost(ipv4Text(address), scan)
                    if (scan.cancelled) break

                    ui.post {
                        if (!destroyed && session === scan && !scan.cancelled) {
                            result?.let {
                                registerDevice(it)
                                displayDevice(it)
                            }

                            scan.completed++
                            checkedHosts = scan.completed
                            txtCheckedCount.text = checkedHosts.toString()
                            progressScan.progress = scan.completed

                            txtStatus.text =
                                "Scanning... ${scan.completed} / ${scan.total}"

                            if (scan.completed == scan.total)
                                finishScan(scan)
                        }
                    }
                }
            }
        }

        scan.executor.shutdown()
        ui.postDelayed(networkMonitor, 1000)
    }

    private val networkMonitor = object : Runnable {
        override fun run() {
            val scan = session ?: return

            if (!isStillConnected(scan.lan))
                stopScan("Network disconnected or changed.")
            else
                ui.postDelayed(this, 1000)
        }
    }

    private fun scanHost(ip: String, scan: ScanSession): NetworkDevice? {
        val own = ip == scan.lan.ip
        var reachable = own
        val ports = mutableListOf<Int>()

        try {
            val address = InetAddress.getByName(ip)

            PORTS.forEach { port ->
                if (scan.cancelled) return null

                when (probePort(address, port, scan)) {
                    2 -> {
                        reachable = true
                        ports += port
                    }
                    1 -> reachable = true
                }
            }

            if (!reachable) return null

            val hostname =
                if (own) localDeviceName()
                else getHostname(ip)

            return NetworkDevice(
                ip,
                if (own) "$hostname (This device)" else hostname,
                hostname,
                getMacAddress(ip, scan.lan.interfaceName),
                determineDeviceType(hostname, ports, own),
                own,
                ports,
                true
            )
        } catch (_: Exception) {
            return null
        }
    }

    private fun probePort(
        address: InetAddress,
        port: Int,
        scan: ScanSession
    ): Int {
        var socket: Socket? = null

        try {
            socket = scan.lan.network.socketFactory.createSocket()
            scan.sockets[socket] = true

            socket.connect(
                InetSocketAddress(address, port),
                CONNECT_TIMEOUT_MS
            )

            return 2
        } catch (e: Exception) {
            var cause: Throwable? = e

            while (cause != null) {
                if (
                    cause is ErrnoException &&
                    cause.errno == OsConstants.ECONNREFUSED
                ) return 1

                cause = cause.cause
            }

            return 0
        } finally {
            socket?.let {
                scan.sockets.remove(it)
                try { it.close() } catch (_: Exception) {}
            }
        }
    }

    // ==================== DEVICE INFO ====================

    private fun getHostname(ip: String): String = try {
        InetAddress.getByName(ip).canonicalHostName.let {
            if (it.isBlank() || it == ip) "Unknown Device" else it
        }
    } catch (_: Exception) {
        "Unknown Device"
    }

    private fun localDeviceName(): String {
        val manufacturer = Build.MANUFACTURER.orEmpty().trim()
        val model = Build.MODEL.orEmpty().trim()

        return if (
            model.toLowerCase(Locale.ROOT)
                .startsWith(manufacturer.toLowerCase(Locale.ROOT))
        ) model
        else "$manufacturer $model".trim()
    }

    private fun getMacAddress(ip: String, iface: String): String {
        if (Build.VERSION.SDK_INT >= 29)
            return "Unavailable (restricted by Android)"

        try {
            File("/proc/net/arp").forEachLine {
                val p = it.trim().split(Regex("\\s+"))

                if (p.size >= 6 && p[0] == ip && p[5] == iface) {
                    val mac = p[3].toUpperCase(Locale.ROOT)

                    if (mac.matches(Regex("^([0-9A-F]{2}:){5}[0-9A-F]{2}$")))
                        return mac
                }
            }
        } catch (_: Exception) {}

        return "Unavailable"
    }

    private fun determineDeviceType(
        hostname: String,
        ports: List<Int>,
        own: Boolean
    ): String {
        if (own) return "Android Phone / Tablet"

        val n = hostname.toLowerCase(Locale.ROOT)

        return when {
            "chromecast" in n || 8008 in ports || 8009 in ports ->
                "Google Cast Device"

            listOf("printer", "laserjet", "epson", "brother").any { it in n } ||
                9100 in ports || 631 in ports ->
                "Printer"

            "roku" in n || "tv" in n ->
                "TV / Streaming Device"

            "iphone" in n || "ipad" in n ->
                "Apple Mobile Device"

            554 in ports ->
                "Camera / Media Device"

            445 in ports || 139 in ports ->
                "Computer / NAS"

            53 in ports && (80 in ports || 443 in ports) ->
                "Router / Network Device"

            22 in ports ->
                "Computer / Network Device"

            80 in ports || 443 in ports || 8080 in ports ->
                "Web / Network Device"

            else ->
                "Unknown Device"
        }
    }

    // ==================== WEB INTERFACE ====================

    private fun getWebInterfaceUrl(device: NetworkDevice): String? = when {
        443 in device.openPorts -> "https://${device.ipAddress}"
        80 in device.openPorts -> "http://${device.ipAddress}"
        8080 in device.openPorts -> "http://${device.ipAddress}:8080"
        else -> null
    }

    private fun openWebInterface(device: NetworkDevice) {
        val url = getWebInterfaceUrl(device) ?: return

        try {
            startActivity(Intent(Intent.ACTION_VIEW, Uri.parse(url)))
        } catch (_: Exception) {
            AlertDialog.Builder(this)
                .setTitle("Unable to open")
                .setMessage("Couldn't open:\n$url")
                .setPositiveButton("OK", null)
                .show()
        }
    }

    // ==================== DEVICE CARDS ====================

    private fun displayDevice(device: NetworkDevice) {
        devices[device.ipAddress] = device

        cards[device.ipAddress]?.let {
            deviceContainer.removeView(it)
        }

        val card = column().apply {
            background = surface(
                panel,
                if (device.isNewDevice) alertColor else border
            )
            setPadding(dp(16), dp(16), dp(16), dp(16))
        }

        val top = row()

        val status = when {
            device.isThisDevice -> "YOU"
            device.isNewDevice -> "NEW"
            else -> "KNOWN"
        }

        val statusColor = when {
            device.isThisDevice -> lime
            device.isNewDevice -> alertColor
            else -> cyan
        }

        top.addView(badge(status, statusColor))

        top.addView(
            label(
                device.deviceName.removeSuffix(" (This device)"),
                16f,
                primaryText,
                false,
                true
            ).apply { setPadding(dp(12), 0, 0, 0) }
        )

        card.addView(top)

        addBlock(card, label(device.ipAddress, 21f, cyan, true, true), 16)
        addBlock(card, label(device.deviceType, 12f, mutedText), 8)

        if (device.isNewDevice)
            addBlock(
                card,
                label("● NEW DEVICE DETECTED", 11f, alertColor, true, true),
                10
            )

        if (device.firstSeen > 0)
            addBlock(
                card,
                label(
                    "First seen · ${formatSeenTime(device.firstSeen)}",
                    11f,
                    mutedText,
                    true
                ),
                8
            )

        val ports = when {
            !device.portsChecked -> "Ports not checked yet"
            device.openPorts.isEmpty() -> "No open ports among those checked"
            else -> device.openPorts.sorted().joinToString("  ·  ") {
                "$it/${getServiceName(it)}"
            }
        }

        addBlock(card, label(ports, 12f, lime, true), 12)

        val inspect = action("Inspect device  →")
        inspect.setOnClickListener {
            devices[device.ipAddress]?.let { showDeviceDetails(it) }
        }

        addBlock(card, inspect, 14)

        cards[device.ipAddress] = card
        deviceContainer.addView(
            card,
            LinearLayout.LayoutParams(-1, -2).apply { topMargin = dp(12) }
        )

        updateMetrics()
    }

    // ==================== DEVICE INSPECTOR ====================

    private fun showDeviceDetails(device: NetworkDevice) {
        val content = column().apply {
            setPadding(dp(22), dp(12), dp(22), dp(12))
        }

        fun field(title: String, value: String) {
            addBlock(content, label(title, 10f, mutedText, true), 18)
            addBlock(
                content,
                label(value, 14f, primaryText, true).apply {
                    setTextIsSelectable(true)
                },
                7
            )
        }

        field(
            "STATUS",
            when {
                device.isThisDevice -> "THIS DEVICE"
                device.isNewDevice -> "NEW DEVICE"
                else -> "KNOWN DEVICE"
            }
        )

        field("IP ADDRESS", device.ipAddress)
        field("HOSTNAME", device.hostname)
        field("MAC ADDRESS", device.macAddress)
        field("DEVICE TYPE · ESTIMATED", device.deviceType)

        if (device.firstSeen > 0)
            field("FIRST SEEN", formatFullTime(device.firstSeen))

        if (device.lastSeen > 0)
            field("LAST SEEN", formatFullTime(device.lastSeen))

        field(
            "OPEN TCP PORTS",
            if (device.openPorts.isEmpty())
                "None detected among checked ports"
            else
                device.openPorts.sorted().joinToString("\n") {
                    "$it  /  ${getServiceName(it)}"
                }
        )

        // NEW WEB INTERFACE FEATURE
        val webUrl = getWebInterfaceUrl(device)

        if (webUrl != null) {
            field("WEB INTERFACE", webUrl)

            val webButton = action("Open Web Interface  →", true)
            webButton.setOnClickListener { openWebInterface(device) }
            addBlock(content, webButton, 20)
        }

        val scroll = ScrollView(this).apply { addView(content) }

        val dialog = AlertDialog.Builder(this)
            .setTitle(device.deviceName.removeSuffix(" (This device)"))
            .setView(scroll)
            .setPositiveButton("Close", null)
            .create()

        inputDialog = dialog
        dialog.show()

        dialog.window?.setBackgroundDrawable(surface())
        dialog.getButton(AlertDialog.BUTTON_POSITIVE).setTextColor(lime)
    }

    // ==================== TIME / SERVICES ====================

    private fun formatSeenTime(time: Long): String {
        val diff = System.currentTimeMillis() - time

        return when {
            diff < 60_000 -> "Just now"
            diff < 3_600_000 -> "${diff / 60_000} min ago"
            diff < 86_400_000 ->
                SimpleDateFormat("h:mm a", Locale.getDefault()).format(Date(time))
            else ->
                SimpleDateFormat("MMM d, h:mm a", Locale.getDefault()).format(Date(time))
        }
    }

    private fun formatFullTime(time: Long) =
        SimpleDateFormat(
            "MMM d, yyyy · h:mm:ss a",
            Locale.getDefault()
        ).format(Date(time))

    private fun getServiceName(port: Int) = when (port) {
        22 -> "SSH"
        53 -> "DNS"
        80 -> "HTTP"
        139 -> "NetBIOS"
        443 -> "HTTPS"
        445 -> "SMB"
        554 -> "RTSP"
        631 -> "IPP"
        8008 -> "Google Cast HTTP"
        8009 -> "Google Cast"
        8080 -> "HTTP Alternate"
        9100 -> "Printer"
        else -> "Unknown"
    }

    // ==================== COMPLETE / STOP ====================

    private fun finishScan(scan: ScanSession) {
        if (session !== scan) return

        ui.removeCallbacks(networkMonitor)
        session = null

        setScanAppearance(false, "COMPLETE")
        progressScan.visibility = View.GONE
        btnScan.text = "Scan again  →"

        val peers = devices.values.count { !it.isThisDevice }
        val newCount = devices.values.count { it.isNewDevice && !it.isThisDevice }

        if (!baselineEstablished) {
            baselineEstablished = true
            preferences.edit().putBoolean(PREF_BASELINE, true).apply()

            devices.values.forEach { it.isNewDevice = false }

            txtResultNote.text =
                "Baseline established · future scans will flag new devices"

            txtStatus.text =
                "Baseline complete - $peers other devices remembered"

            devices.values.toList().forEach { displayDevice(it) }
            return
        }

        txtResultNote.text =
            if (newCount > 0)
                "Scan complete · $newCount new device(s) detected"
            else
                "Scan complete · no new devices detected"

        txtStatus.text =
            "Scan complete - $peers other devices responded"
    }

    private fun stopScan(message: String) {
        val scan = session ?: return

        session = null
        scan.stop()

        ui.removeCallbacks(networkMonitor)

        setScanAppearance(false, "STOPPED")
        progressScan.visibility = View.GONE
        btnScan.text = "Scan again  →"
        btnScan.isEnabled = true
        txtStatus.text = message
        txtResultNote.text = "Partial scan results"
    }

    override fun onStop() {
        inputDialog?.dismiss()
        inputDialog = null
        stopScan("Scan stopped because the app left the screen")
        super.onStop()
    }

    override fun onDestroy() {
        destroyed = true
        session?.stop()
        session = null
        ui.removeCallbacksAndMessages(null)
        super.onDestroy()
    }
}