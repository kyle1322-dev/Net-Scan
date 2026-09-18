package com.kyle.networkscanner

import android.content.Context
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
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.system.ErrnoException
import android.system.OsConstants
import android.text.InputType
import android.view.View
import android.view.Gravity
import android.view.ViewGroup
import android.widget.ScrollView
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.TextView
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import java.io.File
import java.net.Inet4Address
import java.net.InetAddress
import java.net.InetSocketAddress
import java.net.NetworkInterface
import java.net.Socket
import java.util.Locale
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicLong

/*
 * Requires minSdkVersion 21 or later and these manifest permissions:
 * android.permission.INTERNET
 * android.permission.ACCESS_NETWORK_STATE
 *
 * The dashboard is built in Kotlin.
 * No layout XML or drawable files are required.
 *
 * Keep only ONE NetworkDevice declaration in the project.
 */

data class NetworkDevice(
    val ipAddress: String,
    var deviceName: String,
    var hostname: String,
    var macAddress: String,
    var deviceType: String,
    var isThisDevice: Boolean,
    var openPorts: MutableList<Int>,
    var portsChecked: Boolean = false
)

// Long arithmetic prevents signed-Int overflow for IPv4 addresses.
private data class Ipv4Subnet(
    val local: Long,
    val prefix: Int
) {
    init {
        require(local in 0L..0xFFFFFFFFL)
        require(prefix in 0..32)
    }

    val mask: Long =
        (0xFFFFFFFFL shl (32 - prefix)) and 0xFFFFFFFFL

    val network: Long = local and mask

    val broadcast: Long =
        network or (mask xor 0xFFFFFFFFL)

    // /31 links have two usable addresses; /32 has one.
    val first: Long =
        if (prefix >= 31) network else network + 1L

    val last: Long =
        if (prefix >= 31) broadcast else broadcast - 1L

    val hostCount: Long = last - first + 1L

    val cidr: String
        get() = "${ipv4Text(network)}/$prefix"
}

private fun ipv4Number(address: Inet4Address): Long {
    var value = 0L

    for (byte in address.address) {
        value = (value shl 8) or (byte.toLong() and 255L)
    }

    return value
}

private fun ipv4Text(value: Long): String =
    "${(value shr 24) and 255L}.${(value shr 16) and 255L}." +
        "${(value shr 8) and 255L}.${value and 255L}"

private fun parseIpv4(text: String): Long? {
    val parts = text.trim().split(".")

    if (parts.size != 4) return null

    var result = 0L

    for (part in parts) {
        if (part.isEmpty() || part.any { it !in '0'..'9' }) {
            return null
        }

        val octet = part.toIntOrNull() ?: return null

        if (octet !in 0..255) return null

        result = (result shl 8) or octet.toLong()
    }

    return result
}

class MainActivity : AppCompatActivity() {

    // =========================================================
    // UI
    // =========================================================

    private lateinit var txtIpAddress: TextView
    private lateinit var txtSubnet: TextView
    private lateinit var txtStatus: TextView
    private lateinit var txtDevicesFound: TextView
    private lateinit var btnScan: Button
    private lateinit var progressScan: ProgressBar
    private lateinit var deviceContainer: LinearLayout
    private lateinit var connectivity: ConnectivityManager
    private lateinit var txtPortCount: TextView
    private lateinit var txtCheckedCount: TextView
    private lateinit var txtPhase: TextView
    private lateinit var txtTransport: TextView
    private lateinit var txtResultNote: TextView
    private lateinit var emptyState: LinearLayout
    private lateinit var radar: RadarView

    private var checkedHosts = 0
    private var totalHosts = 0

    // =========================================================
    // COLORS
    // =========================================================

    private val ink = Color.rgb(8, 13, 18)
    private val panel = Color.rgb(17, 25, 33)
    private val border = Color.rgb(38, 54, 64)
    private val lime = Color.rgb(190, 255, 89)
    private val cyan = Color.rgb(88, 222, 235)
    private val primaryText = Color.rgb(235, 243, 246)
    private val mutedText = Color.rgb(151, 171, 183)

    // =========================================================
    // STATE
    // =========================================================

    private val ui = Handler(Looper.getMainLooper())
    private val devices = LinkedHashMap<String, NetworkDevice>()
    private val cards = HashMap<String, View>()

    private var selectedLan: Lan? = null
    private var session: ScanSession? = null
    private var destroyed = false
    private var inputDialog: AlertDialog? = null

    companion object {
        private const val WORKERS = 40
        private const val MAX_HOSTS_PER_SCAN = 4096L
        private const val CONNECT_TIMEOUT_MS = 250

        private val PORTS = intArrayOf(
            22,
            53,
            80,
            139,
            443,
            445,
            554,
            631,
            8008,
            8009,
            8080,
            9100
        )
    }

    private data class Lan(
        val network: Network,
        val ip: String,
        val interfaceName: String,
        val transport: String,
        val subnet: Ipv4Subnet
    )

    private class ScanSession(
        val lan: Lan,
        val first: Long,
        val last: Long
    ) {
        val nextAddress = AtomicLong(first)

        val total = (last - first + 1L).toInt()

        val executor =
            Executors.newFixedThreadPool(minOf(WORKERS, total))

        val sockets = ConcurrentHashMap<Socket, Boolean>()

        @Volatile
        var cancelled = false

        // Only the main thread updates this counter.
        var completed = 0

        fun stop() {
            cancelled = true

            for (socket in sockets.keys) {
                try {
                    socket.close()
                } catch (_: Exception) {
                }
            }

            executor.shutdownNow()
        }
    }

    // =========================================================
    // ACTIVITY SETUP
    // =========================================================

    override fun onCreate(savedInstanceState: Bundle?) {
        setTheme(
            androidx.appcompat.R.style.Theme_AppCompat_NoActionBar
        )

        super.onCreate(savedInstanceState)

        buildDashboard()

        connectivity =
            getSystemService(Context.CONNECTIVITY_SERVICE)
                as ConnectivityManager

        btnScan.setOnClickListener {
            if (session != null) {
                stopScan("Scan cancelled")
            } else {
                chooseNetwork()
            }
        }
    }

    // =========================================================
    // UI HELPERS
    // =========================================================

    private fun dp(value: Int): Int =
        (value * resources.displayMetrics.density + 0.5f).toInt()

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
        value: String,
        size: Float = 14f,
        color: Int = primaryText,
        mono: Boolean = false,
        bold: Boolean = false
    ) = TextView(this).apply {
        text = value
        textSize = size
        setTextColor(color)

        typeface = Typeface.create(
            if (mono) "monospace" else "sans-serif",
            if (bold) Typeface.BOLD else Typeface.NORMAL
        )

        includeFontPadding = false
        setLineSpacing(dp(3).toFloat(), 1f)
    }

    private fun column() = LinearLayout(this).apply {
        orientation = LinearLayout.VERTICAL
    }

    private fun row() = LinearLayout(this).apply {
        orientation = LinearLayout.HORIZONTAL
        gravity = Gravity.CENTER_VERTICAL
    }

    private fun addBlock(
        parent: LinearLayout,
        child: View,
        gap: Int = 12
    ) {
        parent.addView(
            child,
            LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            ).apply {
                topMargin = dp(gap)
            }
        )
    }

    private fun badge(
        value: String,
        color: Int = cyan
    ) = label(
        value,
        11f,
        color,
        true,
        true
    ).apply {
        background = surface(panel, border, 8)
        setPadding(dp(10), dp(7), dp(10), dp(7))
    }

    private fun action(
        value: String,
        filled: Boolean = false
    ) = Button(this).apply {
        text = value
        textSize = 13f
        typeface = Typeface.create("monospace", Typeface.BOLD)
        isAllCaps = false

        setTextColor(if (filled) ink else cyan)

        minHeight = dp(50)
        minimumHeight = dp(50)
        minWidth = 0
        minimumWidth = 0

        setPadding(dp(16), dp(10), dp(16), dp(10))

        // Remove theme tint so the terminal palette stays consistent.
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

        val number = label("0", 26f, color, true, true)

        box.addView(number)

        addBlock(
            box,
            label(title, 10f, mutedText, true),
            8
        )

        parent.addView(
            box,
            LinearLayout.LayoutParams(
                0,
                ViewGroup.LayoutParams.MATCH_PARENT,
                1f
            ).apply {
                if (gap) marginStart = dp(8)
            }
        )

        return number
    }

    // =========================================================
    // DASHBOARD
    // =========================================================

    @Suppress("DEPRECATION")
    private fun buildDashboard() {
        // Compatible with the project's older AndroidX dependencies.
        window.clearFlags(
            android.view.WindowManager.LayoutParams.FLAG_TRANSLUCENT_STATUS or
                android.view.WindowManager.LayoutParams.FLAG_TRANSLUCENT_NAVIGATION
        )

        window.addFlags(
            android.view.WindowManager.LayoutParams.FLAG_DRAWS_SYSTEM_BAR_BACKGROUNDS
        )

        // Normal window bounds and light icons on dark system bars.
        window.decorView.systemUiVisibility =
            View.SYSTEM_UI_FLAG_VISIBLE

        window.statusBarColor = ink
        window.navigationBarColor = ink

        val root = column().apply {
            setBackgroundColor(ink)
            fitsSystemWindows = true
        }

        val scroll = ScrollView(this).apply {
            isFillViewport = true
            isVerticalScrollBarEnabled = false
            overScrollMode = View.OVER_SCROLL_NEVER
        }

        val content = column().apply {
            setPadding(dp(20), dp(24), dp(20), dp(28))
        }

        scroll.addView(content)

        root.addView(
            scroll,
            LinearLayout.LayoutParams(-1, -1)
        )

        setContentView(root)
        root.requestApplyInsets()

        // Header
        val header = row()

        header.addView(
            label("[ N ]", 23f, lime, true, true)
        )

        val brand = column().apply {
            setPadding(dp(12), 0, 0, 0)
        }

        brand.addView(
            label(
                "NET / SCANNER",
                17f,
                primaryText,
                false,
                true
            )
        )

        addBlock(
            brand,
            label(
                "LOCAL NETWORK CONSOLE",
                10f,
                mutedText,
                true
            ),
            5
        )

        header.addView(
            brand,
            LinearLayout.LayoutParams(0, -2, 1f)
        )

        content.addView(header)

        addBlock(
            content,
            label(
                "Network overview",
                28f,
                primaryText,
                false,
                true
            ),
            28
        )

        addBlock(
            content,
            label(
                "Discover devices. Inspect services.",
                14f,
                mutedText
            ),
            8
        )

        // Network overview card
        val hero = column().apply {
            background = surface()
            setPadding(dp(18), dp(18), dp(18), dp(18))
        }

        val heroTop = row()

        txtPhase = label(
            "●  STANDBY",
            12f,
            lime,
            true,
            true
        )

        heroTop.addView(
            txtPhase,
            LinearLayout.LayoutParams(0, -2, 1f)
        )

        txtTransport = badge("NO LINK")

        heroTop.addView(txtTransport)
        hero.addView(heroTop)

        radar = RadarView(this)

        hero.addView(
            radar,
            LinearLayout.LayoutParams(-1, dp(154)).apply {
                topMargin = dp(8)
            }
        )

        txtIpAddress = label(
            "No local IPv4",
            22f,
            primaryText,
            true,
            true
        )

        addBlock(
            hero,
            label("LOCAL ADDRESS", 10f, mutedText, true),
            4
        )

        addBlock(hero, txtIpAddress, 8)

        txtSubnet = label(
            "Connect to Wi-Fi or Ethernet",
            12f,
            mutedText,
            true
        )

        addBlock(hero, txtSubnet, 10)
        addBlock(content, hero, 24)

        // Metrics
        val metrics = row()

        txtDevicesFound = metric(
            metrics,
            "DEVICES",
            lime,
            false
        )

        txtPortCount = metric(
            metrics,
            "OPEN PORTS",
            cyan,
            true
        )

        txtCheckedCount = metric(
            metrics,
            "CHECKED",
            primaryText,
            true
        )

        addBlock(content, metrics, 12)

        // Scan controls
        val scanPanel = column().apply {
            background = surface()
            setPadding(dp(16), dp(16), dp(16), dp(16))
        }

        scanPanel.addView(
            label(">_ SCAN SESSION", 11f, cyan, true, true)
        )

        txtStatus = label(
            "Waiting for a local network",
            13f,
            primaryText,
            true
        )

        addBlock(scanPanel, txtStatus, 12)

        progressScan = ProgressBar(
            this,
            null,
            android.R.attr.progressBarStyleHorizontal
        ).apply {
            isIndeterminate = false

            progressTintList =
                ColorStateList.valueOf(lime)

            progressBackgroundTintList =
                ColorStateList.valueOf(border)

            visibility = View.GONE
        }

        scanPanel.addView(
            progressScan,
            LinearLayout.LayoutParams(-1, dp(8)).apply {
                topMargin = dp(12)
            }
        )

        btnScan = action("Start scan  →", true)

        addBlock(scanPanel, btnScan, 16)
        addBlock(content, scanPanel, 12)

        // Results
        addBlock(
            content,
            label(
                "Discovered devices",
                20f,
                primaryText,
                false,
                true
            ),
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

        emptyState.addView(
            label("[  ·  ·  ·  ]", 24f, cyan, true)
        )

        addBlock(
            emptyState,
            label(
                "Your network, mapped here",
                16f,
                primaryText,
                false,
                true
            ).apply {
                gravity = Gravity.CENTER
            },
            16
        )

        addBlock(
            emptyState,
            label(
                "Start a scan to see device addresses and services.",
                13f,
                mutedText
            ).apply {
                gravity = Gravity.CENTER
            },
            8
        )

        addBlock(content, emptyState, 14)

        deviceContainer = column()

        addBlock(content, deviceContainer, 2)

        addBlock(
            content,
            label(
                "Results are a snapshot of the last scan.\n" +
                    "Open ports are detected services, not a security verdict.",
                11f,
                mutedText
            ),
            20
        )
    }

    private fun updateMetrics() {
        txtDevicesFound.text = devices.size.toString()

        txtPortCount.text = devices.values.fold(0) { sum, device ->
            sum + device.openPorts.size
        }.toString()

        txtCheckedCount.text = checkedHosts.toString()

        txtCheckedCount.contentDescription =
            "$checkedHosts of $totalHosts addresses checked"

        txtDevicesFound.contentDescription =
            "${devices.size} devices, including this device"

        txtPortCount.contentDescription =
            "${txtPortCount.text} open TCP ports across all devices"

        emptyState.visibility =
            if (devices.isEmpty()) View.VISIBLE else View.GONE
    }

    private fun setScanAppearance(
        scanning: Boolean,
        phase: String
    ) {
        txtPhase.text = "●  $phase"

        txtPhase.setTextColor(
            if (scanning) lime else cyan
        )

        radar.setScanning(scanning)

        btnScan.setTextColor(
            if (scanning) primaryText else ink
        )

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

    // =========================================================
    // DECORATIVE RADAR
    // =========================================================

    private inner class RadarView(
        context: Context
    ) : View(context) {

        private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
        private val bounds = RectF()
        private var scanning = false

        init {
            importantForAccessibility =
                View.IMPORTANT_FOR_ACCESSIBILITY_NO
        }

        fun setScanning(value: Boolean) {
            scanning = value
            invalidate()
        }

        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)

            val cx = width / 2f
            val cy = height / 2f
            val radius = minOf(width, height) * 0.42f

            paint.shader = null
            paint.style = Paint.Style.STROKE
            paint.strokeWidth = resources.displayMetrics.density
            paint.color = border

            for (ring in 1..3) {
                canvas.drawCircle(
                    cx,
                    cy,
                    radius * ring / 3f,
                    paint
                )
            }

            canvas.drawLine(
                cx - radius,
                cy,
                cx + radius,
                cy,
                paint
            )

            canvas.drawLine(
                cx,
                cy - radius,
                cx,
                cy + radius,
                paint
            )

            bounds.set(
                cx - radius,
                cy - radius,
                cx + radius,
                cy + radius
            )

            val angle = if (scanning) {
                (SystemClock.uptimeMillis() % 2800L) *
                    360f / 2800f
            } else {
                -45f
            }

            paint.color = cyan
            paint.strokeWidth = dp(2).toFloat()

            canvas.drawArc(
                bounds,
                angle - 65f,
                65f,
                false,
                paint
            )

            if (scanning) {
                paint.style = Paint.Style.FILL
                paint.color = 0x163ADDCD

                canvas.drawArc(
                    bounds,
                    angle - 65f,
                    65f,
                    true,
                    paint
                )
            }

            paint.style = Paint.Style.FILL
            paint.color = lime

            canvas.drawCircle(
                cx,
                cy,
                dp(4).toFloat(),
                paint
            )

            if (scanning && isShown) {
                postInvalidateOnAnimation()
            }
        }
    }

    // =========================================================
    // NETWORK DETECTION
    // =========================================================

    override fun onResume() {
        super.onResume()

        if (session == null) {
            refreshNetwork()
        }
    }

    private fun isLan(
        capabilities: NetworkCapabilities
    ): Boolean {
        return !capabilities.hasTransport(
            NetworkCapabilities.TRANSPORT_VPN
        ) &&
            capabilities.hasCapability(
                NetworkCapabilities.NET_CAPABILITY_NOT_VPN
            ) &&
            (
                capabilities.hasTransport(
                    NetworkCapabilities.TRANSPORT_WIFI
                ) ||
                    capabilities.hasTransport(
                        NetworkCapabilities.TRANSPORT_ETHERNET
                    )
                )
    }

    @Suppress("DEPRECATION")
    private fun availableLans(): List<Lan> {
        val result = ArrayList<Lan>()

        // Internet validation is not required.
        // A local network can be usable without internet access.
        for (network in connectivity.allNetworks) {
            val capabilities =
                connectivity.getNetworkCapabilities(network)
                    ?: continue

            if (!isLan(capabilities)) continue

            val links =
                connectivity.getLinkProperties(network)
                    ?: continue

            val interfaceName = links.interfaceName ?: continue

            val transport = if (
                capabilities.hasTransport(
                    NetworkCapabilities.TRANSPORT_WIFI
                )
            ) {
                "Wi-Fi"
            } else {
                "Ethernet"
            }

            for (link in links.linkAddresses) {
                val address =
                    link.address as? Inet4Address ?: continue

                if (
                    address.isLoopbackAddress ||
                    address.isAnyLocalAddress ||
                    address.isMulticastAddress
                ) {
                    continue
                }

                val ip = address.hostAddress ?: continue

                result.add(
                    Lan(
                        network,
                        ip,
                        interfaceName,
                        transport,
                        Ipv4Subnet(
                            ipv4Number(address),
                            link.prefixLength
                        )
                    )
                )
            }
        }

        val active = if (Build.VERSION.SDK_INT >= 23) {
            connectivity.activeNetwork
        } else {
            null
        }

        return result.sortedWith(
            compareBy<Lan>(
                { if (it.network == active) 0 else 1 },
                { if (it.transport == "Wi-Fi") 0 else 1 },
                { it.interfaceName },
                { it.ip }
            )
        )
    }

    private fun refreshNetwork(): List<Lan> {
        val lans = try {
            availableLans()
        } catch (_: SecurityException) {
            selectedLan = null

            txtIpAddress.text = "Unavailable"
            txtTransport.text = "NO LINK"

            setScanAppearance(false, "UNAVAILABLE")

            txtSubnet.text = "Subnet: Unavailable"

            txtStatus.text =
                "Add ACCESS_NETWORK_STATE to AndroidManifest.xml"

            btnScan.text = "Retry"

            return emptyList()
        }

        val previous = selectedLan

        val selected =
            lans.firstOrNull { it == previous } ?: lans.firstOrNull()

        selectedLan = selected
        btnScan.isEnabled = true

        if (selected == null) {
            txtIpAddress.text = "No local IPv4"
            txtTransport.text = "NO LINK"

            setScanAppearance(false, "OFFLINE")

            txtSubnet.text = "Subnet: Not detected"

            txtStatus.text =
                "Connect to Wi-Fi or Ethernet with IPv4, then tap Retry"

            btnScan.text = "Retry"
        } else {
            showNetwork(selected)

            txtStatus.text = "Ready to scan ${selected.transport}"
            btnScan.text = "Start scan  →"

            setScanAppearance(false, "READY")
        }

        return lans
    }

    private fun showNetwork(lan: Lan) {
        txtIpAddress.text = lan.ip

        txtTransport.text =
            lan.transport.toUpperCase(Locale.ROOT)

        txtSubnet.text =
            "${lan.subnet.cidr}\n" +
                "Mask: ${ipv4Text(lan.subnet.mask)}"
    }

    private fun chooseNetwork() {
        val lans = refreshNetwork()

        if (lans.isEmpty()) return

        if (lans.size == 1) {
            chooseRange(lans[0])
        } else {
            val labels = lans.map {
                "${it.transport} (${it.interfaceName})\n" +
                    "${it.ip} - ${it.subnet.cidr}"
            }.toTypedArray()

            inputDialog = AlertDialog.Builder(this)
                .setTitle("Choose a local network")
                .setItems(labels) { _, index ->
                    chooseRange(lans[index])
                }
                .setNegativeButton("Cancel", null)
                .show()
        }
    }

    private fun chooseRange(lan: Lan) {
        selectedLan = lan
        showNetwork(lan)

        if (lan.subnet.hostCount <= MAX_HOSTS_PER_SCAN) {
            startScan(
                lan,
                lan.subnet.first,
                lan.subnet.last
            )

            return
        }

        // Let the user choose a bounded part of the actual subnet.
        val block = lan.subnet.local and 0xFFFFFF00L
        val first = maxOf(lan.subnet.first, block)
        val last = minOf(lan.subnet.last, block + 255L)

        val layout = LinearLayout(this)
        layout.orientation = LinearLayout.VERTICAL

        val padding =
            (20 * resources.displayMetrics.density).toInt()

        layout.setPadding(padding, 0, padding, 0)

        val startInput = EditText(this)
        startInput.hint = "First IPv4 address"
        startInput.inputType = InputType.TYPE_CLASS_TEXT
        startInput.setText(ipv4Text(first))

        val endInput = EditText(this)
        endInput.hint = "Last IPv4 address"
        endInput.inputType = InputType.TYPE_CLASS_TEXT
        endInput.setText(ipv4Text(last))

        layout.addView(startInput)
        layout.addView(endInput)

        val dialog = AlertDialog.Builder(this)
            .setTitle("Choose a scan range")
            .setMessage(
                "${lan.subnet.cidr} contains " +
                    "${lan.subnet.hostCount} host addresses. " +
                    "Scan up to $MAX_HOSTS_PER_SCAN at a time. " +
                    "Change this range to scan other parts."
            )
            .setView(layout)
            .setPositiveButton("Scan", null)
            .setNegativeButton("Cancel", null)
            .create()

        inputDialog = dialog

        dialog.setOnShowListener {
            dialog.getButton(
                AlertDialog.BUTTON_POSITIVE
            ).setOnClickListener {
                val from =
                    parseIpv4(startInput.text.toString())

                val to =
                    parseIpv4(endInput.text.toString())

                when {
                    from == null ||
                        from !in lan.subnet.first..lan.subnet.last -> {
                        startInput.error =
                            "Enter an address inside ${lan.subnet.cidr}"
                    }

                    to == null ||
                        to !in lan.subnet.first..lan.subnet.last -> {
                        endInput.error =
                            "Enter an address inside ${lan.subnet.cidr}"
                    }

                    to < from -> {
                        endInput.error =
                            "Must be at or after the first address"
                    }

                    to - from + 1L > MAX_HOSTS_PER_SCAN -> {
                        endInput.error =
                            "Maximum $MAX_HOSTS_PER_SCAN addresses per scan"
                    }

                    else -> {
                        dialog.dismiss()
                        startScan(lan, from, to)
                    }
                }
            }
        }

        dialog.show()
    }

    private fun isStillConnected(lan: Lan): Boolean {
        return try {
            val capabilities =
                connectivity.getNetworkCapabilities(lan.network)

            val links =
                connectivity.getLinkProperties(lan.network)

            capabilities != null &&
                isLan(capabilities) &&
                links != null &&
                links.interfaceName == lan.interfaceName &&
                links.linkAddresses.any {
                    it.address.hostAddress == lan.ip &&
                        it.prefixLength == lan.subnet.prefix
                }
        } catch (_: SecurityException) {
            false
        }
    }

    // =========================================================
    // SCANNING
    // =========================================================

    private fun startScan(
        lan: Lan,
        first: Long,
        last: Long
    ) {
        if (!isStillConnected(lan)) {
            refreshNetwork()

            txtStatus.text =
                "Network changed. Tap Scan or Retry to refresh."

            return
        }

        val scan = ScanSession(lan, first, last)
        session = scan

        devices.clear()
        cards.clear()
        deviceContainer.removeAllViews()

        checkedHosts = 0
        totalHosts = scan.total

        updateMetrics()
        setScanAppearance(true, "SCANNING")

        txtResultNote.text =
            "Current scan · includes this device"

        showNetwork(lan)

        txtSubnet.append(
            "\nScan range: ${ipv4Text(first)} - ${ipv4Text(last)}"
        )

        progressScan.max = scan.total
        progressScan.progress = 0
        progressScan.visibility = View.VISIBLE

        btnScan.text = "Stop scan  ■"
        btnScan.isEnabled = true

        txtStatus.text = "Scanning... 0 / ${scan.total}"

        // Always show this phone using the known local address.
        val phoneName = localDeviceName()

        displayDevice(
            NetworkDevice(
                lan.ip,
                "$phoneName (This device)",
                phoneName,
                getMacAddress(lan.ip, lan.interfaceName),
                "Android Phone / Tablet",
                true,
                mutableListOf()
            )
        )

        repeat(minOf(WORKERS, scan.total)) {
            scan.executor.execute {
                while (
                    !scan.cancelled &&
                    !Thread.currentThread().isInterrupted
                ) {
                    val value =
                        scan.nextAddress.getAndIncrement()

                    if (value > scan.last) break

                    val result =
                        scanHost(ipv4Text(value), scan)

                    if (scan.cancelled) break

                    ui.post {
                        if (
                            !destroyed &&
                            session === scan &&
                            !scan.cancelled
                        ) {
                            if (result != null) {
                                displayDevice(result)
                            }

                            scan.completed++
                            checkedHosts = scan.completed

                            txtCheckedCount.text =
                                checkedHosts.toString()

                            txtCheckedCount.contentDescription =
                                "$checkedHosts of $totalHosts addresses checked"

                            progressScan.progress = scan.completed

                            txtStatus.text =
                                "Scanning... ${scan.completed} / ${scan.total}"

                            if (scan.completed == scan.total) {
                                finishScan(scan)
                            }
                        }
                    }
                }
            }
        }

        // Only a bounded number of worker jobs are queued.
        scan.executor.shutdown()

        ui.postDelayed(networkMonitor, 1000L)
    }

    private val networkMonitor = object : Runnable {
        override fun run() {
            val scan = session ?: return

            if (!isStillConnected(scan.lan)) {
                stopScan(
                    "Network disconnected or changed. Tap Scan to refresh."
                )
            } else {
                ui.postDelayed(this, 1000L)
            }
        }
    }

    private fun scanHost(
        ip: String,
        scan: ScanSession
    ): NetworkDevice? {
        val thisDevice = ip == scan.lan.ip

        var reachable = thisDevice

        val openPorts = mutableListOf<Int>()

        try {
            val address = InetAddress.getByName(ip)

            // Java reachability cannot bind to an Android Network.
            // Use it only on the default LAN without a visible VPN.
            // TCP probes below use the selected Network.
            if (
                !reachable &&
                canUseDefaultNetworkProbe(scan.lan)
            ) {
                try {
                    val iface = NetworkInterface.getByName(
                        scan.lan.interfaceName
                    )

                    if (
                        iface != null &&
                        address.isReachable(iface, 0, 400)
                    ) {
                        reachable = true
                    }
                } catch (_: Exception) {
                }
            }

            for (port in PORTS) {
                if (
                    scan.cancelled ||
                    Thread.currentThread().isInterrupted
                ) {
                    return null
                }

                when (probePort(address, port, scan)) {
                    2 -> {
                        reachable = true
                        openPorts.add(port)
                    }

                    // Explicit refusal is still a response.
                    1 -> reachable = true
                }
            }

            if (!reachable || scan.cancelled) return null

            val hostname = if (thisDevice) {
                localDeviceName()
            } else {
                getHostname(ip, scan)
            }

            return NetworkDevice(
                ip,
                if (thisDevice) {
                    "$hostname (This device)"
                } else {
                    hostname
                },
                hostname,
                getMacAddress(ip, scan.lan.interfaceName),
                determineDeviceType(
                    hostname,
                    openPorts,
                    thisDevice
                ),
                thisDevice,
                openPorts,
                true
            )
        } catch (_: Exception) {
            // The local phone card remains visible.
            return null
        }
    }

    @Suppress("DEPRECATION")
    private fun canUseDefaultNetworkProbe(
        lan: Lan
    ): Boolean = try {
        Build.VERSION.SDK_INT >= 23 &&
            connectivity.activeNetwork == lan.network &&
            connectivity.allNetworks.none {
                connectivity.getNetworkCapabilities(it)
                    ?.hasTransport(
                        NetworkCapabilities.TRANSPORT_VPN
                    ) == true
            }
    } catch (_: Exception) {
        false
    }

    // Returns:
    // 2 = open
    // 1 = refused
    // 0 = no conclusive response
    private fun probePort(
        address: InetAddress,
        port: Int,
        scan: ScanSession
    ): Int {
        var socket: Socket? = null

        try {
            socket = scan.lan.network.socketFactory.createSocket()

            scan.sockets[socket] = true

            if (scan.cancelled) return 0

            socket.connect(
                InetSocketAddress(address, port),
                CONNECT_TIMEOUT_MS
            )

            return 2
        } catch (error: Exception) {
            var cause: Throwable? = error

            while (cause != null) {
                if (
                    cause is ErrnoException &&
                    cause.errno == OsConstants.ECONNREFUSED
                ) {
                    return 1
                }

                cause = cause.cause
            }

            return 0
        } finally {
            if (socket != null) {
                scan.sockets.remove(socket)

                try {
                    socket.close()
                } catch (_: Exception) {
                }
            }
        }
    }

    // =========================================================
    // DEVICE INFORMATION
    // =========================================================

    private fun getHostname(
        ip: String,
        scan: ScanSession
    ): String {
        // Skip system reverse DNS when it may use another network.
        if (!canUseDefaultNetworkProbe(scan.lan)) {
            return "Unknown Device"
        }

        return try {
            val name =
                InetAddress.getByName(ip).canonicalHostName

            if (name.isNullOrBlank() || name == ip) {
                "Unknown Device"
            } else {
                name
            }
        } catch (_: Exception) {
            "Unknown Device"
        }
    }

    private fun localDeviceName(): String {
        val manufacturer =
            Build.MANUFACTURER.orEmpty().trim()

        val model = Build.MODEL.orEmpty().trim()

        if (manufacturer.isEmpty()) {
            return if (model.isEmpty()) {
                "Android device"
            } else {
                model
            }
        }

        if (
            model.toLowerCase(Locale.ROOT).startsWith(
                manufacturer.toLowerCase(Locale.ROOT)
            )
        ) {
            return model
        }

        return (
            manufacturer.substring(0, 1)
                .toUpperCase(Locale.ROOT) +
                manufacturer.substring(1) +
                " " +
                model
            ).trim()
    }

    private fun getMacAddress(
        ip: String,
        interfaceName: String
    ): String {
        if (Build.VERSION.SDK_INT >= 29) {
            return "Unavailable (restricted by Android)"
        }

        try {
            File("/proc/net/arp").bufferedReader().use { reader ->
                while (true) {
                    val line = reader.readLine() ?: break

                    val parts =
                        line.trim().split(Regex("\\s+"))

                    if (
                        parts.size < 6 ||
                        parts[0] != ip ||
                        parts[5] != interfaceName
                    ) {
                        continue
                    }

                    val flags = parts[2]
                        .removePrefix("0x")
                        .toIntOrNull(16) ?: 0

                    val mac =
                        parts[3].toUpperCase(Locale.ROOT)

                    if (
                        (flags and 2) != 0 &&
                        mac.matches(
                            Regex("^([0-9A-F]{2}:){5}[0-9A-F]{2}$")
                        ) &&
                        mac != "00:00:00:00:00:00" &&
                        mac != "FF:FF:FF:FF:FF:FF" &&
                        mac != "02:00:00:00:00:00"
                    ) {
                        return mac
                    }
                }
            }
        } catch (_: Exception) {
        }

        return "Unavailable"
    }

    private fun determineDeviceType(
        hostname: String,
        ports: List<Int>,
        own: Boolean
    ): String {
        if (own) return "Android Phone / Tablet"

        val name = hostname.toLowerCase(Locale.ROOT)

        return when {
            name.contains("chromecast") ||
                name.contains("googlecast") -> {
                "Chromecast / Google Cast"
            }

            listOf(
                "printer",
                "laserjet",
                "epson",
                "brother"
            ).any { name.contains(it) } -> {
                "Printer"
            }

            name.contains("roku") || name.contains("tv") -> {
                "TV / Streaming Device"
            }

            name.contains("iphone") || name.contains("ipad") -> {
                "Apple Mobile Device"
            }

            8008 in ports || 8009 in ports -> {
                "Google Cast Device"
            }

            9100 in ports || 631 in ports -> {
                "Network Printer"
            }

            554 in ports -> {
                "Camera / Media Device"
            }

            445 in ports || 139 in ports -> {
                "Computer / NAS"
            }

            53 in ports && (80 in ports || 443 in ports) -> {
                "Router / Network Device"
            }

            22 in ports -> {
                "Computer / Network Device"
            }

            80 in ports || 443 in ports || 8080 in ports -> {
                "Web / Network Device"
            }

            else -> "Unknown Device"
        }
    }

    // =========================================================
    // DEVICE CARDS
    // =========================================================

    private fun displayDevice(device: NetworkDevice) {
        devices[device.ipAddress] = device

        val old = cards[device.ipAddress]

        val position = if (old == null) {
            -1
        } else {
            deviceContainer.indexOfChild(old)
        }

        if (old != null) {
            deviceContainer.removeView(old)
        }

        val card = column().apply {
            background = surface()
            setPadding(dp(16), dp(16), dp(16), dp(16))
        }

        val top = row()

        val marker = badge(
            if (device.isThisDevice) "YOU" else "LAN",
            if (device.isThisDevice) lime else cyan
        )

        top.addView(marker)

        val title = label(
            device.deviceName.removeSuffix(" (This device)"),
            16f,
            primaryText,
            false,
            true
        ).apply {
            setPadding(dp(12), 0, 0, 0)
        }

        top.addView(
            title,
            LinearLayout.LayoutParams(0, -2, 1f)
        )

        card.addView(top)

        addBlock(
            card,
            label(
                device.ipAddress,
                21f,
                cyan,
                true,
                true
            ),
            16
        )

        addBlock(
            card,
            label(
                if (device.isThisDevice) {
                    "This Android device"
                } else {
                    "Estimated type · ${device.deviceType}"
                },
                12f,
                mutedText
            ),
            8
        )

        val portSummary = when {
            !device.portsChecked -> {
                "Ports not checked yet"
            }

            device.openPorts.isEmpty() -> {
                "No open ports among those checked"
            }

            else -> {
                device.openPorts.sorted().joinToString("  ·  ") {
                    "$it/${getServiceName(it)}"
                }
            }
        }

        addBlock(
            card,
            label(portSummary, 12f, lime, true),
            12
        )

        val footer = action("Inspect device  →")

        footer.contentDescription =
            "Inspect ${device.deviceName}, ${device.ipAddress}"

        footer.setOnClickListener {
            devices[device.ipAddress]?.let {
                showDeviceDetails(it)
            }
        }

        addBlock(card, footer, 14)

        cards[device.ipAddress] = card

        val params = LinearLayout.LayoutParams(-1, -2).apply {
            topMargin = dp(12)
        }

        if (position >= 0) {
            deviceContainer.addView(card, position, params)
        } else {
            deviceContainer.addView(card, params)
        }

        updateMetrics()
    }

    private fun showDeviceDetails(device: NetworkDevice) {
        val content = column().apply {
            setPadding(dp(22), dp(12), dp(22), dp(12))
        }

        fun field(title: String, value: String) {
            addBlock(
                content,
                label(title, 10f, mutedText, true),
                18
            )

            addBlock(
                content,
                label(
                    value,
                    14f,
                    primaryText,
                    true
                ).apply {
                    setTextIsSelectable(true)
                },
                7
            )
        }

        field("IP ADDRESS", device.ipAddress)
        field("HOSTNAME", device.hostname)
        field("MAC ADDRESS", device.macAddress)
        field("DEVICE TYPE · ESTIMATED", device.deviceType)

        field(
            "OBSERVATION",
            if (device.isThisDevice) {
                "This device"
            } else {
                "Responded during this scan"
            }
        )

        field(
            "OPEN TCP PORTS",
            when {
                !device.portsChecked -> {
                    "Not checked yet / outside selected scan range"
                }

                device.openPorts.isEmpty() -> {
                    "None detected among the checked ports"
                }

                else -> {
                    device.openPorts.sorted().joinToString("\n") {
                        "$it  /  ${getServiceName(it)}"
                    }
                }
            }
        )

        field(
            "SERVICE IDENTIFICATION",
            "Service names are inferred from port numbers."
        )

        val scroll = ScrollView(this).apply {
            addView(content)
        }

        val dialog = AlertDialog.Builder(this)
            .setTitle(
                device.deviceName.removeSuffix(" (This device)")
            )
            .setView(scroll)
            .setPositiveButton("Close", null)
            .create()

        inputDialog = dialog

        dialog.show()

        dialog.window?.setBackgroundDrawable(surface())

        dialog.getButton(
            AlertDialog.BUTTON_POSITIVE
        ).setTextColor(lime)
    }

    private fun getServiceName(port: Int): String = when (port) {
        22 -> "SSH"
        53 -> "DNS"
        80 -> "HTTP"
        139 -> "NetBIOS"
        443 -> "HTTPS"
        445 -> "SMB"
        554 -> "RTSP"
        631 -> "IPP Printing"
        8008 -> "Google Cast HTTP"
        8009 -> "Google Cast"
        8080 -> "HTTP Alternate"
        9100 -> "Printer"
        else -> "Unknown Service"
    }

    // =========================================================
    // COMPLETION AND CLEANUP
    // =========================================================

    private fun finishScan(scan: ScanSession) {
        if (session !== scan) return

        if (!isStillConnected(scan.lan)) {
            stopScan(
                "Network disconnected or changed; results are incomplete."
            )

            return
        }

        ui.removeCallbacks(networkMonitor)

        session = null

        setScanAppearance(false, "COMPLETE")

        txtResultNote.text =
            "Last completed scan · includes this device"

        progressScan.visibility = View.GONE
        btnScan.text = "Scan again  →"

        val peers = devices.values.count {
            !it.isThisDevice
        }

        val partial =
            scan.first != scan.lan.subnet.first ||
                scan.last != scan.lan.subnet.last

        txtStatus.text = if (partial) {
            "Selected range complete - $peers other devices responded"
        } else {
            "Subnet scan complete - $peers other devices responded"
        }
    }

    private fun stopScan(message: String) {
        val scan = session ?: return

        // Ignore late results from this session.
        session = null

        scan.stop()

        setScanAppearance(false, "STOPPED")

        txtResultNote.text =
            "Partial scan results · includes this device"

        ui.removeCallbacks(networkMonitor)

        progressScan.visibility = View.GONE
        btnScan.text = "Scan again  →"
        btnScan.isEnabled = true
        txtStatus.text = message
    }

    override fun onStop() {
        inputDialog?.dismiss()
        inputDialog = null

        stopScan(
            "Scan stopped because the app left the screen"
        )

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