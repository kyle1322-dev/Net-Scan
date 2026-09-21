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
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.ScrollView
import android.widget.TextView
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import androidx.core.app.NotificationCompat
import androidx.core.app.NotificationManagerCompat
import androidx.core.content.ContextCompat
import java.io.File
import java.net.Inet4Address
import java.net.InetAddress
import java.net.InetSocketAddress
import java.net.Socket
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicLong

// ============================================================
// DEVICE MODELS
// ============================================================

/**
 * A device displayed in the current scan.
 *
 * Device type is estimated from its hostname and open ports.
 * An open port does not definitively identify a device.
 */
data class NetworkDevice(
    val ipAddress: String,
    var deviceName: String,
    var hostname: String,
    var macAddress: String,
    var deviceType: String,
    var isThisDevice: Boolean,
    var openPorts: MutableList<Int>,

    // False while the local device is displayed before probing.
    var portsChecked: Boolean = false,

    // True when first observed after the baseline was established.
    var isNewDevice: Boolean = false,

    // Unix timestamps in milliseconds.
    var firstSeen: Long = 0L,
    var lastSeen: Long = 0L
)

/**
 * Information retained between scans.
 *
 * This implementation identifies remembered devices by IP address.
 * DHCP address changes can therefore affect NEW / KNOWN labels.
 */
private data class KnownDevice(
    val ipAddress: String,
    var hostname: String,
    var macAddress: String,
    var deviceType: String,
    var firstSeen: Long,
    var lastSeen: Long
)

// ============================================================
// IPV4 SUBNET CALCULATIONS
// ============================================================

/**
 * Stores the address boundaries of an IPv4 subnet.
 *
 * Long is used because IPv4 addresses are unsigned 32-bit values.
 * Kotlin Int is signed and cannot directly represent every IPv4
 * address as a positive number.
 */
private data class Ipv4Subnet(
    val local: Long,
    val prefix: Int
) {
    // Keep only the lowest 32 bits after creating the subnet mask.
    val mask: Long =
        (0xFFFFFFFFL shl (32 - prefix)) and 0xFFFFFFFFL

    // The network address has all host bits cleared.
    val network: Long =
        local and mask

    // The broadcast address has all host bits set.
    val broadcast: Long =
        network or (mask xor 0xFFFFFFFFL)

    // /31 and /32 networks do not use the usual host exclusions.
    val first: Long =
        if (prefix >= 31) {
            network
        } else {
            network + 1
        }

    val last: Long =
        if (prefix >= 31) {
            broadcast
        } else {
            broadcast - 1
        }

    val hostCount: Long =
        last - first + 1

    val cidr: String
        get() {
            return "${ipv4Text(network)}/$prefix"
        }
}

/**
 * Converts an IPv4 address into a positive numeric value.
 */
private fun ipv4Number(address: Inet4Address): Long {
    var value = 0L

    for (addressByte in address.address) {
        // Convert the signed byte to an unsigned value: 0 through 255.
        val unsignedByte = addressByte.toLong() and 255L

        // Move existing octets left before appending the next octet.
        value = (value shl 8) or unsignedByte
    }

    return value
}

/**
 * Converts a numeric IPv4 address back into dotted decimal.
 */
private fun ipv4Text(value: Long): String {
    val firstOctet = (value shr 24) and 255L
    val secondOctet = (value shr 16) and 255L
    val thirdOctet = (value shr 8) and 255L
    val fourthOctet = value and 255L

    return "$firstOctet.$secondOctet.$thirdOctet.$fourthOctet"
}

/**
 * Parses a dotted IPv4 address.
 *
 * Returns null when the input does not contain four valid octets.
 */
private fun parseIpv4(text: String): Long? {
    val parts = text.trim().split(".")

    if (parts.size != 4) {
        return null
    }

    var result = 0L

    for (part in parts) {
        val octet = part.toIntOrNull() ?: return null

        if (octet !in 0..255) {
            return null
        }

        result = (result shl 8) or octet.toLong()
    }

    return result
}

// ============================================================
// MAIN ACTIVITY
// ============================================================

class MainActivity : AppCompatActivity() {

    // --------------------------------------------------------
    // DASHBOARD VIEWS
    // --------------------------------------------------------

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
    private lateinit var radar: RadarView

    // --------------------------------------------------------
    // ANDROID SERVICES
    // --------------------------------------------------------

    private lateinit var connectivity: ConnectivityManager
    private lateinit var preferences: SharedPreferences

    // --------------------------------------------------------
    // DASHBOARD COLORS
    // --------------------------------------------------------

    private val ink = Color.rgb(8, 13, 18)
    private val panel = Color.rgb(17, 25, 33)
    private val border = Color.rgb(38, 54, 64)

    private val lime = Color.rgb(190, 255, 89)
    private val cyan = Color.rgb(88, 222, 235)

    private val primaryText = Color.rgb(235, 243, 246)
    private val mutedText = Color.rgb(151, 171, 183)
    private val alertColor = Color.rgb(255, 190, 80)

    // --------------------------------------------------------
    // APPLICATION STATE
    // --------------------------------------------------------

    // Worker threads post dashboard updates through this handler.
    private val ui = Handler(Looper.getMainLooper())

    // LinkedHashMap retains the order devices are inserted.
    private val devices = LinkedHashMap<String, NetworkDevice>()

    // Associates an IP address with its current dashboard card.
    private val cards = HashMap<String, View>()

    // Devices remembered from previous observations.
    private val knownDevices = LinkedHashMap<String, KnownDevice>()

    // Prevents duplicate alerts for an address within one scan.
    private val notifiedThisScan = HashSet<String>()

    private var checkedHosts = 0

    private var selectedLan: Lan? = null
    private var session: ScanSession? = null

    private var destroyed = false
    private var baselineEstablished = false

    private var inputDialog: AlertDialog? = null

    // --------------------------------------------------------
    // CONSTANTS
    // --------------------------------------------------------

    companion object {
        // Maximum number of simultaneous host-scanning workers.
        private const val WORKERS = 40

        // Prevents accidentally scanning an extremely large subnet.
        private const val MAX_HOSTS_PER_SCAN = 4096L

        // Timeout for each TCP connection attempt.
        private const val CONNECT_TIMEOUT_MS = 250

        private const val PREFS_NAME = "net_scanner_devices"
        private const val PREF_BASELINE = "baseline_established"
        private const val PREF_DEVICE_SET = "known_devices"

        private const val CHANNEL_ID = "new_device_alerts"
        private const val CHANNEL_NAME = "New Device Alerts"

        private const val NOTIFICATION_REQUEST = 1001

        private const val POST_NOTIFICATIONS_PERMISSION =
            "android.permission.POST_NOTIFICATIONS"

        // These are the only TCP ports checked by this scanner.
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

    // --------------------------------------------------------
    // NETWORK AND SCAN MODELS
    // --------------------------------------------------------

    /**
     * One usable IPv4 address on a Wi-Fi or Ethernet network.
     *
     * The Network object lets sockets use the selected network.
     */
    private data class Lan(
        val network: Network,
        val ip: String,
        val interfaceName: String,
        val transport: String,
        val subnet: Ipv4Subnet
    )

    /**
     * Holds all resources belonging to one scan.
     */
    private class ScanSession(
        val lan: Lan,
        val first: Long,
        val last: Long
    ) {
        // Workers claim addresses atomically to avoid duplicates.
        val nextAddress = AtomicLong(first)

        val total: Int =
            (last - first + 1).toInt()

        val executor =
            Executors.newFixedThreadPool(minOf(WORKERS, total))

        // Tracks sockets so cancellation can close active probes.
        val sockets = ConcurrentHashMap<Socket, Boolean>()

        @Volatile
        var cancelled = false

        // Updated only on the main thread.
        var completed = 0

        fun stop() {
            cancelled = true

            for (socket in sockets.keys) {
                try {
                    socket.close()
                } catch (_: Exception) {
                    // Continue closing the remaining sockets.
                }
            }

            executor.shutdownNow()
        }
    }

    // ========================================================
    // ACTIVITY INITIALIZATION
    // ========================================================

    override fun onCreate(savedInstanceState: Bundle?) {
        setTheme(
            androidx.appcompat.R.style.Theme_AppCompat_NoActionBar
        )

        super.onCreate(savedInstanceState)

        buildDashboard()

        connectivity =
            getSystemService(Context.CONNECTIVITY_SERVICE)
                as ConnectivityManager

        preferences = getSharedPreferences(
            PREFS_NAME,
            MODE_PRIVATE
        )

        baselineEstablished = preferences.getBoolean(
            PREF_BASELINE,
            false
        )

        loadKnownDevices()
        createNotificationChannel()
        requestNotificationPermission()

        btnScan.setOnClickListener {
            if (session != null) {
                stopScan("Scan cancelled")
            } else {
                chooseNetwork()
            }
        }
    }

    // ========================================================
    // SAVED DEVICE HISTORY
    // ========================================================

    /**
     * Reads saved device records.
     *
     * Record layout:
     * IP | hostname | MAC | type | firstSeen | lastSeen
     */
    private fun loadKnownDevices() {
        knownDevices.clear()

        val savedRecords = preferences.getStringSet(
            PREF_DEVICE_SET,
            emptySet()
        ) ?: return

        for (record in savedRecords) {
            try {
                val parts = record.split("|")

                if (parts.size < 6) {
                    continue
                }

                val firstSeen =
                    parts[4].toLongOrNull() ?: continue

                val lastSeen =
                    parts[5].toLongOrNull() ?: firstSeen

                val knownDevice = KnownDevice(
                    ipAddress = parts[0],
                    hostname = parts[1],
                    macAddress = parts[2],
                    deviceType = parts[3],
                    firstSeen = firstSeen,
                    lastSeen = lastSeen
                )

                knownDevices[knownDevice.ipAddress] = knownDevice
            } catch (_: Exception) {
                // Ignore an unreadable record and load the rest.
            }
        }
    }

    /**
     * Serializes the remembered devices into SharedPreferences.
     */
    private fun saveKnownDevices() {
        val savedRecords = knownDevices.values.map { device ->
            // Remove delimiters from values before serialization.
            val hostname = device.hostname.replace("|", " ")
            val macAddress = device.macAddress.replace("|", " ")
            val deviceType = device.deviceType.replace("|", " ")

            "${device.ipAddress}|$hostname|$macAddress|" +
                "$deviceType|${device.firstSeen}|${device.lastSeen}"
        }.toSet()

        preferences.edit()
            .putStringSet(PREF_DEVICE_SET, savedRecords)
            .apply()
    }

    /**
     * Updates history and determines whether to send an alert.
     *
     * Called on the main thread when a device is discovered.
     */
    private fun registerDevice(device: NetworkDevice) {
        val now = System.currentTimeMillis()
        val previousRecord = knownDevices[device.ipAddress]

        if (previousRecord != null) {
            device.isNewDevice = false
            device.firstSeen = previousRecord.firstSeen
            device.lastSeen = now

            previousRecord.hostname = device.hostname
            previousRecord.macAddress = device.macAddress
            previousRecord.deviceType = device.deviceType
            previousRecord.lastSeen = now
        } else {
            device.firstSeen = now
            device.lastSeen = now

            // The first completed scan establishes the baseline.
            device.isNewDevice =
                baselineEstablished && !device.isThisDevice

            knownDevices[device.ipAddress] = KnownDevice(
                ipAddress = device.ipAddress,
                hostname = device.hostname,
                macAddress = device.macAddress,
                deviceType = device.deviceType,
                firstSeen = now,
                lastSeen = now
            )

            if (
                device.isNewDevice &&
                notifiedThisScan.add(device.ipAddress)
            ) {
                showNewDeviceNotification(device)
            }
        }

        if (device.isThisDevice) {
            device.isNewDevice = false
        }

        saveKnownDevices()
    }

    // ========================================================
    // NOTIFICATIONS
    // ========================================================

    private fun createNotificationChannel() {
        // Notification channels are available from Android 8.
        if (Build.VERSION.SDK_INT < 26) {
            return
        }

        val channel = NotificationChannel(
            CHANNEL_ID,
            CHANNEL_NAME,
            NotificationManager.IMPORTANCE_HIGH
        ).apply {
            description =
                "Alerts when a new device appears on the local network"

            enableVibration(true)
        }

        val notificationManager =
            getSystemService(Context.NOTIFICATION_SERVICE)
                as NotificationManager

        notificationManager.createNotificationChannel(channel)
    }

    private fun requestNotificationPermission() {
        // Android 13 introduced the notification runtime permission.
        if (Build.VERSION.SDK_INT < 33) {
            return
        }

        val permissionResult = ContextCompat.checkSelfPermission(
            this,
            POST_NOTIFICATIONS_PERMISSION
        )

        if (permissionResult != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(
                arrayOf(POST_NOTIFICATIONS_PERMISSION),
                NOTIFICATION_REQUEST
            )
        }
    }

    private fun showNewDeviceNotification(device: NetworkDevice) {
        if (Build.VERSION.SDK_INT >= 33) {
            val permissionResult =
                ContextCompat.checkSelfPermission(
                    this,
                    POST_NOTIFICATIONS_PERMISSION
                )

            if (
                permissionResult != PackageManager.PERMISSION_GRANTED
            ) {
                return
            }
        }

        val expandedMessage =
            "A previously unseen device responded on your network.\n\n" +
                "IP: ${device.ipAddress}\n" +
                "Device: ${device.hostname}\n" +
                "Type: ${device.deviceType}"

        val notification = NotificationCompat.Builder(
            this,
            CHANNEL_ID
        )
            .setSmallIcon(android.R.drawable.stat_notify_sync)
            .setContentTitle("New device detected")
            .setContentText(
                "${device.ipAddress} · ${device.deviceType}"
            )
            .setStyle(
                NotificationCompat.BigTextStyle()
                    .bigText(expandedMessage)
            )
            .setPriority(NotificationCompat.PRIORITY_HIGH)
            .setAutoCancel(true)
            .build()

        val notificationId =
            device.ipAddress.hashCode() and 0x7FFFFFFF

        try {
            NotificationManagerCompat.from(this)
                .notify(notificationId, notification)
        } catch (_: SecurityException) {
            // The scan remains usable if notifications are denied.
        }
    }

    // ========================================================
    // REUSABLE UI HELPERS
    // ========================================================

    /**
     * Converts density-independent pixels into physical pixels.
     */
    private fun dp(value: Int): Int {
        val density = resources.displayMetrics.density
        return (value * density + 0.5f).toInt()
    }

    private fun surface(
        fill: Int = panel,
        stroke: Int = border,
        radius: Int = 20
    ): GradientDrawable {
        return GradientDrawable().apply {
            setColor(fill)
            cornerRadius = dp(radius).toFloat()
            setStroke(dp(1), stroke)
        }
    }

    private fun label(
        textValue: String,
        size: Float = 14f,
        color: Int = primaryText,
        mono: Boolean = false,
        bold: Boolean = false
    ): TextView {
        val fontFamily =
            if (mono) "monospace" else "sans-serif"

        val fontStyle =
            if (bold) Typeface.BOLD else Typeface.NORMAL

        return TextView(this).apply {
            text = textValue
            textSize = size
            setTextColor(color)
            typeface = Typeface.create(fontFamily, fontStyle)
            includeFontPadding = false
        }
    }

    private fun column(): LinearLayout {
        return LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
        }
    }

    private fun row(): LinearLayout {
        return LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }
    }

    /**
     * Adds a full-width view with a top margin.
     */
    private fun addBlock(
        parent: LinearLayout,
        view: View,
        gap: Int = 12
    ) {
        val layoutParameters = LinearLayout.LayoutParams(
            LinearLayout.LayoutParams.MATCH_PARENT,
            LinearLayout.LayoutParams.WRAP_CONTENT
        ).apply {
            topMargin = dp(gap)
        }

        parent.addView(view, layoutParameters)
    }

    private fun badge(
        text: String,
        color: Int = cyan
    ): TextView {
        return label(
            textValue = text,
            size = 11f,
            color = color,
            mono = true,
            bold = true
        ).apply {
            background = surface(panel, border, 8)
            setPadding(dp(10), dp(7), dp(10), dp(7))
        }
    }

    private fun action(
        text: String,
        filled: Boolean = false
    ): Button {
        val backgroundColor =
            if (filled) lime else panel

        val outlineColor =
            if (filled) lime else border

        val foregroundColor =
            if (filled) ink else cyan

        return Button(this).apply {
            this.text = text
            textSize = 13f
            isAllCaps = false

            typeface = Typeface.create(
                "monospace",
                Typeface.BOLD
            )

            setTextColor(foregroundColor)

            minHeight = dp(50)
            minimumHeight = dp(50)
            backgroundTintList = null

            background = RippleDrawable(
                ColorStateList.valueOf(0x3368DDEB),
                surface(
                    fill = backgroundColor,
                    stroke = outlineColor,
                    radius = 12
                ),
                null
            )

            stateListAnimator = null
        }
    }

    /**
     * Creates one dashboard metric and returns its value label.
     */
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

        val value = label(
            textValue = "0",
            size = 26f,
            color = color,
            mono = true,
            bold = true
        )

        box.addView(value)

        addBlock(
            box,
            label(title, 10f, mutedText, true),
            8
        )

        val layoutParameters = LinearLayout.LayoutParams(
            0,
            LinearLayout.LayoutParams.MATCH_PARENT,
            1f
        ).apply {
            if (gap) {
                marginStart = dp(8)
            }
        }

        parent.addView(box, layoutParameters)

        return value
    }

    // ========================================================
    // DASHBOARD CONSTRUCTION
    // ========================================================

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

        root.addView(
            scroll,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.MATCH_PARENT
            )
        )

        setContentView(root)

        // ----------------------------------------------------
        // Branding and title
        // ----------------------------------------------------

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

        header.addView(brand)
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
                "Discover devices. Inspect services. Detect changes.",
                14f,
                mutedText
            ),
            8
        )

        // ----------------------------------------------------
        // Network summary and radar
        // ----------------------------------------------------

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
            LinearLayout.LayoutParams(
                0,
                LinearLayout.LayoutParams.WRAP_CONTENT,
                1f
            )
        )

        txtTransport = badge("NO LINK")
        heroTop.addView(txtTransport)
        hero.addView(heroTop)

        radar = RadarView(this)

        hero.addView(
            radar,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                dp(154)
            )
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

        // ----------------------------------------------------
        // Numeric scan metrics
        // ----------------------------------------------------

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

        // ----------------------------------------------------
        // Scan controls
        // ----------------------------------------------------

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
            progressTintList = ColorStateList.valueOf(lime)
            progressBackgroundTintList =
                ColorStateList.valueOf(border)

            visibility = View.GONE
        }

        scanPanel.addView(
            progressScan,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                dp(8)
            ).apply {
                topMargin = dp(12)
            }
        )

        btnScan = action("Start scan  →", true)

        addBlock(scanPanel, btnScan, 16)
        addBlock(content, scanPanel, 12)

        // ----------------------------------------------------
        // Device results
        // ----------------------------------------------------

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
            ),
            16
        )

        addBlock(
            emptyState,
            label(
                "Start a scan to see device addresses and services.",
                13f,
                mutedText
            ),
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

        var openPortCount = 0

        for (device in devices.values) {
            openPortCount += device.openPorts.size
        }

        txtPortCount.text = openPortCount.toString()
        txtCheckedCount.text = checkedHosts.toString()

        emptyState.visibility =
            if (devices.isEmpty()) {
                View.VISIBLE
            } else {
                View.GONE
            }
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
                fill = if (scanning) panel else lime,
                stroke = if (scanning) cyan else lime,
                radius = 12
            ),
            null
        )
    }

    // ========================================================
    // ANIMATED RADAR
    // ========================================================

    /**
     * Decorative scan animation.
     *
     * The radar does not represent physical device positions.
     */
    private inner class RadarView(
        context: Context
    ) : View(context) {

        private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
        private val bounds = RectF()

        private var scanning = false

        fun setScanning(value: Boolean) {
            scanning = value
            invalidate()
        }

        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)

            val centerX = width / 2f
            val centerY = height / 2f
            val radius = minOf(width, height) * 0.42f

            // Draw the circular grid.
            paint.style = Paint.Style.STROKE
            paint.strokeWidth = resources.displayMetrics.density
            paint.color = border

            for (ring in 1..3) {
                val ringRadius = radius * ring / 3f

                canvas.drawCircle(
                    centerX,
                    centerY,
                    ringRadius,
                    paint
                )
            }

            // Horizontal and vertical crosshairs.
            canvas.drawLine(
                centerX - radius,
                centerY,
                centerX + radius,
                centerY,
                paint
            )

            canvas.drawLine(
                centerX,
                centerY - radius,
                centerX,
                centerY + radius,
                paint
            )

            bounds.set(
                centerX - radius,
                centerY - radius,
                centerX + radius,
                centerY + radius
            )

            // Complete one revolution every 2.8 seconds.
            val angle =
                if (scanning) {
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

            // Center marker.
            paint.style = Paint.Style.FILL
            paint.color = lime

            canvas.drawCircle(
                centerX,
                centerY,
                dp(4).toFloat(),
                paint
            )

            if (scanning && isShown) {
                postInvalidateOnAnimation()
            }
        }
    }

    // ========================================================
    // LOCAL NETWORK DISCOVERY
    // ========================================================

    override fun onResume() {
        super.onResume()

        if (session == null) {
            refreshNetwork()
        }
    }

    /**
     * Accepts Wi-Fi and Ethernet networks while excluding VPNs.
     */
    private fun isLan(capabilities: NetworkCapabilities): Boolean {
        val isVpn = capabilities.hasTransport(
            NetworkCapabilities.TRANSPORT_VPN
        )

        val isNotVpn = capabilities.hasCapability(
            NetworkCapabilities.NET_CAPABILITY_NOT_VPN
        )

        val isWifi = capabilities.hasTransport(
            NetworkCapabilities.TRANSPORT_WIFI
        )

        val isEthernet = capabilities.hasTransport(
            NetworkCapabilities.TRANSPORT_ETHERNET
        )

        return !isVpn && isNotVpn && (isWifi || isEthernet)
    }

    @Suppress("DEPRECATION")
    private fun availableLans(): List<Lan> {
        val results = arrayListOf<Lan>()

        for (network in connectivity.allNetworks) {
            val capabilities =
                connectivity.getNetworkCapabilities(network)
                    ?: continue

            if (!isLan(capabilities)) {
                continue
            }

            val linkProperties =
                connectivity.getLinkProperties(network)
                    ?: continue

            val interfaceName =
                linkProperties.interfaceName ?: continue

            val transport =
                if (
                    capabilities.hasTransport(
                        NetworkCapabilities.TRANSPORT_WIFI
                    )
                ) {
                    "Wi-Fi"
                } else {
                    "Ethernet"
                }

            for (linkAddress in linkProperties.linkAddresses) {
                val address =
                    linkAddress.address as? Inet4Address
                        ?: continue

                if (
                    address.isLoopbackAddress ||
                    address.isAnyLocalAddress ||
                    address.isMulticastAddress
                ) {
                    continue
                }

                val ipAddress = address.hostAddress ?: continue

                val subnet = Ipv4Subnet(
                    local = ipv4Number(address),
                    prefix = linkAddress.prefixLength
                )

                results.add(
                    Lan(
                        network = network,
                        ip = ipAddress,
                        interfaceName = interfaceName,
                        transport = transport,
                        subnet = subnet
                    )
                )
            }
        }

        return results
    }

    private fun refreshNetwork(): List<Lan> {
        val networks = try {
            availableLans()
        } catch (_: Exception) {
            emptyList<Lan>()
        }

        selectedLan = networks.firstOrNull()
        val currentLan = selectedLan

        if (currentLan == null) {
            txtIpAddress.text = "No local IPv4"
            txtTransport.text = "NO LINK"
            txtSubnet.text = "Subnet: Not detected"
            txtStatus.text = "Connect to Wi-Fi or Ethernet"

            btnScan.text = "Retry"
            setScanAppearance(false, "OFFLINE")
        } else {
            showNetwork(currentLan)

            txtStatus.text =
                "Ready to scan ${currentLan.transport}"

            btnScan.text = "Start scan  →"
            setScanAppearance(false, "READY")
        }

        return networks
    }

    @Suppress("DEPRECATION")
    private fun showNetwork(lan: Lan) {
        txtIpAddress.text = lan.ip
        txtTransport.text = lan.transport.toUpperCase(Locale.ROOT)

        txtSubnet.text =
            "${lan.subnet.cidr}\n" +
                "Mask: ${ipv4Text(lan.subnet.mask)}"
    }

    private fun chooseNetwork() {
        val networks = refreshNetwork()

        if (networks.isEmpty()) {
            return
        }

        if (networks.size == 1) {
            chooseRange(networks[0])
            return
        }

        val labels = networks.map { lan ->
            "${lan.transport} (${lan.interfaceName})\n" +
                "${lan.ip} - ${lan.subnet.cidr}"
        }.toTypedArray()

        AlertDialog.Builder(this)
            .setTitle("Choose a local network")
            .setItems(labels) { _, index ->
                chooseRange(networks[index])
            }
            .setNegativeButton("Cancel", null)
            .show()
    }

    // ========================================================
    // SCAN RANGE SELECTION
    // ========================================================

    private fun chooseRange(lan: Lan) {
        selectedLan = lan

        if (lan.subnet.hostCount <= MAX_HOSTS_PER_SCAN) {
            startScan(
                lan = lan,
                first = lan.subnet.first,
                last = lan.subnet.last
            )

            return
        }

        // Suggest the /24-sized block containing the local address.
        val localBlock = lan.subnet.local and 0xFFFFFF00L

        val suggestedFirst = maxOf(
            lan.subnet.first,
            localBlock
        )

        val suggestedLast = minOf(
            lan.subnet.last,
            localBlock + 255L
        )

        val layout = column().apply {
            setPadding(dp(20), 0, dp(20), 0)
        }

        val firstAddressInput = EditText(this).apply {
            hint = "First IPv4 address"
            inputType = InputType.TYPE_CLASS_TEXT
            setText(ipv4Text(suggestedFirst))
        }

        val lastAddressInput = EditText(this).apply {
            hint = "Last IPv4 address"
            inputType = InputType.TYPE_CLASS_TEXT
            setText(ipv4Text(suggestedLast))
        }

        layout.addView(firstAddressInput)
        layout.addView(lastAddressInput)

        val dialog = AlertDialog.Builder(this)
            .setTitle("Choose scan range")
            .setView(layout)
            .setPositiveButton("Scan", null)
            .setNegativeButton("Cancel", null)
            .create()

        // Replacing the listener prevents automatic dismissal
        // when an invalid address needs to be corrected.
        dialog.setOnShowListener {
            val scanButton = dialog.getButton(
                AlertDialog.BUTTON_POSITIVE
            )

            scanButton.setOnClickListener {
                val firstAddress = parseIpv4(
                    firstAddressInput.text.toString()
                )

                val lastAddress = parseIpv4(
                    lastAddressInput.text.toString()
                )

                when {
                    firstAddress == null ||
                        firstAddress !in
                        lan.subnet.first..lan.subnet.last -> {
                        firstAddressInput.error = "Invalid address"
                    }

                    lastAddress == null ||
                        lastAddress !in
                        lan.subnet.first..lan.subnet.last -> {
                        lastAddressInput.error = "Invalid address"
                    }

                    lastAddress < firstAddress -> {
                        lastAddressInput.error =
                            "Must be after first address"
                    }

                    lastAddress - firstAddress + 1 >
                        MAX_HOSTS_PER_SCAN -> {
                        lastAddressInput.error =
                            "Maximum $MAX_HOSTS_PER_SCAN addresses"
                    }

                    else -> {
                        dialog.dismiss()

                        startScan(
                            lan,
                            firstAddress,
                            lastAddress
                        )
                    }
                }
            }
        }

        dialog.show()
    }

    /**
     * Checks that the selected Network and interface remain usable.
     */
    private fun isStillConnected(lan: Lan): Boolean {
        return try {
            val capabilities =
                connectivity.getNetworkCapabilities(lan.network)

            val linkProperties =
                connectivity.getLinkProperties(lan.network)

            capabilities != null &&
                isLan(capabilities) &&
                linkProperties?.interfaceName == lan.interfaceName
        } catch (_: Exception) {
            false
        }
    }

    // ========================================================
    // SCAN EXECUTION
    // ========================================================

    private fun startScan(
        lan: Lan,
        first: Long,
        last: Long
    ) {
        if (!isStillConnected(lan)) {
            refreshNetwork()
            return
        }

        val scan = ScanSession(lan, first, last)
        session = scan

        // Clear results from the previous scan.
        devices.clear()
        cards.clear()
        notifiedThisScan.clear()
        deviceContainer.removeAllViews()

        checkedHosts = 0
        updateMetrics()

        setScanAppearance(true, "SCANNING")

        txtResultNote.text =
            if (baselineEstablished) {
                "Current scan · watching for new devices"
            } else {
                "First scan · establishing device baseline"
            }

        progressScan.max = scan.total
        progressScan.progress = 0
        progressScan.visibility = View.VISIBLE

        btnScan.text = "Stop scan  ■"
        txtStatus.text = "Scanning... 0 / ${scan.total}"

        // Display this phone immediately while probing continues.
        val phoneName = localDeviceName()

        val localDevice = NetworkDevice(
            ipAddress = lan.ip,
            deviceName = "$phoneName (This device)",
            hostname = phoneName,
            macAddress = getMacAddress(
                lan.ip,
                lan.interfaceName
            ),
            deviceType = "Android Phone / Tablet",
            isThisDevice = true,
            openPorts = mutableListOf()
        )

        registerDevice(localDevice)
        displayDevice(localDevice)

        val workerCount = minOf(WORKERS, scan.total)

        repeat(workerCount) {
            scan.executor.execute {
                while (
                    !scan.cancelled &&
                    !Thread.currentThread().isInterrupted
                ) {
                    val nextAddress =
                        scan.nextAddress.getAndIncrement()

                    if (nextAddress > scan.last) {
                        break
                    }

                    val ipAddress = ipv4Text(nextAddress)
                    val result = scanHost(ipAddress, scan)

                    if (scan.cancelled) {
                        break
                    }

                    // All UI and device-map changes happen here,
                    // on the main thread.
                    ui.post {
                        if (
                            !destroyed &&
                            session === scan &&
                            !scan.cancelled
                        ) {
                            if (result != null) {
                                registerDevice(result)
                                displayDevice(result)
                            }

                            scan.completed++
                            checkedHosts = scan.completed

                            txtCheckedCount.text =
                                checkedHosts.toString()

                            progressScan.progress =
                                scan.completed

                            txtStatus.text =
                                "Scanning... ${scan.completed} / " +
                                    "${scan.total}"

                            if (scan.completed == scan.total) {
                                finishScan(scan)
                            }
                        }
                    }
                }
            }
        }

        // Existing worker tasks continue; no new tasks are accepted.
        scan.executor.shutdown()

        ui.postDelayed(networkMonitor, 1000L)
    }

    /**
     * Checks the selected network once per second during a scan.
     */
    private val networkMonitor = object : Runnable {
        override fun run() {
            val currentScan = session ?: return

            if (!isStillConnected(currentScan.lan)) {
                stopScan("Network disconnected or changed.")
            } else {
                ui.postDelayed(this, 1000L)
            }
        }
    }

    /**
     * Probes one address and builds its display model.
     *
     * Devices that silently drop every probe may not be detected.
     */
    private fun scanHost(
        ipAddress: String,
        scan: ScanSession
    ): NetworkDevice? {
        val isLocalDevice = ipAddress == scan.lan.ip

        var reachable = isLocalDevice
        val openPorts = mutableListOf<Int>()

        return try {
            val address = InetAddress.getByName(ipAddress)

            for (port in PORTS) {
                if (scan.cancelled) {
                    return null
                }

                val result = probePort(address, port, scan)

                when (result) {
                    2 -> {
                        reachable = true
                        openPorts.add(port)
                    }

                    1 -> {
                        // Connection refusal is also a response.
                        reachable = true
                    }
                }
            }

            if (!reachable) {
                return null
            }

            val hostname =
                if (isLocalDevice) {
                    localDeviceName()
                } else {
                    getHostname(ipAddress)
                }

            val displayName =
                if (isLocalDevice) {
                    "$hostname (This device)"
                } else {
                    hostname
                }

            NetworkDevice(
                ipAddress = ipAddress,
                deviceName = displayName,
                hostname = hostname,
                macAddress = getMacAddress(
                    ipAddress,
                    scan.lan.interfaceName
                ),
                deviceType = determineDeviceType(
                    hostname,
                    openPorts,
                    isLocalDevice
                ),
                isThisDevice = isLocalDevice,
                openPorts = openPorts,
                portsChecked = true
            )
        } catch (_: Exception) {
            null
        }
    }

    /**
     * Attempts a TCP connection through the selected network.
     *
     * Return values:
     * 0 = no usable response
     * 1 = connection refused
     * 2 = connection succeeded
     */
    private fun probePort(
        address: InetAddress,
        port: Int,
        scan: ScanSession
    ): Int {
        var socket: Socket? = null

        try {
            val probeSocket =
                scan.lan.network.socketFactory.createSocket()

            socket = probeSocket
            scan.sockets[probeSocket] = true

            probeSocket.connect(
                InetSocketAddress(address, port),
                CONNECT_TIMEOUT_MS
            )

            return 2
        } catch (exception: Exception) {
            // Android may wrap the underlying errno exception.
            var cause: Throwable? = exception

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
            val socketToClose = socket

            if (socketToClose != null) {
                scan.sockets.remove(socketToClose)

                try {
                    socketToClose.close()
                } catch (_: Exception) {
                    // The socket may already be closed by stop().
                }
            }
        }
    }

    // ========================================================
    // DEVICE IDENTIFICATION
    // ========================================================

    /**
     * Attempts reverse DNS resolution.
     *
     * Many home devices do not have a resolvable hostname.
     */
    private fun getHostname(ipAddress: String): String {
        return try {
            val hostname =
                InetAddress.getByName(ipAddress).canonicalHostName

            if (hostname.isBlank() || hostname == ipAddress) {
                "Unknown Device"
            } else {
                hostname
            }
        } catch (_: Exception) {
            "Unknown Device"
        }
    }

    @Suppress("DEPRECATION")
    private fun localDeviceName(): String {
        val manufacturer = Build.MANUFACTURER.orEmpty().trim()
        val model = Build.MODEL.orEmpty().trim()

        val normalizedManufacturer =
            manufacturer.toLowerCase(Locale.ROOT)

        val normalizedModel =
            model.toLowerCase(Locale.ROOT)

        return if (
            normalizedModel.startsWith(normalizedManufacturer)
        ) {
            model
        } else {
            "$manufacturer $model".trim()
        }
    }

    /**
     * Attempts to read a matching entry from the ARP table.
     *
     * Android 10 and later restrict this source.
     */
    @Suppress("DEPRECATION")
    private fun getMacAddress(
        ipAddress: String,
        interfaceName: String
    ): String {
        if (Build.VERSION.SDK_INT >= 29) {
            return "Unavailable (restricted by Android)"
        }

        val macPattern = Regex(
            "^([0-9A-F]{2}:){5}[0-9A-F]{2}$"
        )

        try {
            File("/proc/net/arp").bufferedReader().use { reader ->
                while (true) {
                    val line = reader.readLine() ?: break
                    val parts = line.trim().split(Regex("\\s+"))

                    if (
                        parts.size >= 6 &&
                        parts[0] == ipAddress &&
                        parts[5] == interfaceName
                    ) {
                        val macAddress =
                            parts[3].toUpperCase(Locale.ROOT)

                        if (macAddress.matches(macPattern)) {
                            return macAddress
                        }
                    }
                }
            }
        } catch (_: Exception) {
            // Some Android versions or devices block ARP access.
        }

        return "Unavailable"
    }

    /**
     * Uses simple hostname and port heuristics.
     *
     * The order matters: the first matching category wins.
     */
    @Suppress("DEPRECATION")
    private fun determineDeviceType(
        hostname: String,
        ports: List<Int>,
        isLocalDevice: Boolean
    ): String {
        if (isLocalDevice) {
            return "Android Phone / Tablet"
        }

        val normalizedName =
            hostname.toLowerCase(Locale.ROOT)

        val printerKeywords = listOf(
            "printer",
            "laserjet",
            "epson",
            "brother"
        )

        val hasPrinterName = printerKeywords.any { keyword ->
            keyword in normalizedName
        }

        return when {
            "chromecast" in normalizedName ||
                8008 in ports ||
                8009 in ports -> {
                "Google Cast Device"
            }

            hasPrinterName ||
                9100 in ports ||
                631 in ports -> {
                "Printer"
            }

            "roku" in normalizedName ||
                "tv" in normalizedName -> {
                "TV / Streaming Device"
            }

            "iphone" in normalizedName ||
                "ipad" in normalizedName -> {
                "Apple Mobile Device"
            }

            554 in ports -> {
                "Camera / Media Device"
            }

            445 in ports || 139 in ports -> {
                "Computer / NAS"
            }

            53 in ports &&
                (80 in ports || 443 in ports) -> {
                "Router / Network Device"
            }

            22 in ports -> {
                "Computer / Network Device"
            }

            80 in ports ||
                443 in ports ||
                8080 in ports -> {
                "Web / Network Device"
            }

            else -> {
                "Unknown Device"
            }
        }
    }

    // ========================================================
    // WEB INTERFACE
    // ========================================================

    /**
     * Selects a likely web URL based on open TCP ports.
     *
     * Prefers HTTPS, then HTTP, then HTTP on port 8080.
     * An open port alone does not confirm a browser-compatible UI.
     */
    private fun getWebInterfaceUrl(
        device: NetworkDevice
    ): String? {
        return when {
            443 in device.openPorts -> {
                "https://${device.ipAddress}"
            }

            80 in device.openPorts -> {
                "http://${device.ipAddress}"
            }

            8080 in device.openPorts -> {
                "http://${device.ipAddress}:8080"
            }

            else -> {
                null
            }
        }
    }

    private fun openWebInterface(device: NetworkDevice) {
        val url = getWebInterfaceUrl(device) ?: return

        val browserIntent = Intent(
            Intent.ACTION_VIEW,
            Uri.parse(url)
        )

        try {
            startActivity(browserIntent)
        } catch (_: Exception) {
            AlertDialog.Builder(this)
                .setTitle("Unable to open")
                .setMessage("Couldn't open:\n$url")
                .setPositiveButton("OK", null)
                .show()
        }
    }

    // ========================================================
    // DEVICE CARDS
    // ========================================================

    private fun displayDevice(device: NetworkDevice) {
        devices[device.ipAddress] = device

        // Replace the old card if this address already exists.
        val previousCard = cards[device.ipAddress]

        if (previousCard != null) {
            deviceContainer.removeView(previousCard)
        }

        val outlineColor =
            if (device.isNewDevice) alertColor else border

        val card = column().apply {
            background = surface(
                fill = panel,
                stroke = outlineColor
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

        val deviceTitle = label(
            device.deviceName.removeSuffix(" (This device)"),
            16f,
            primaryText,
            false,
            true
        ).apply {
            setPadding(dp(12), 0, 0, 0)
        }

        top.addView(deviceTitle)
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
            label(device.deviceType, 12f, mutedText),
            8
        )

        if (device.isNewDevice) {
            addBlock(
                card,
                label(
                    "● NEW DEVICE DETECTED",
                    11f,
                    alertColor,
                    true,
                    true
                ),
                10
            )
        }

        if (device.firstSeen > 0L) {
            val firstSeenText =
                "First seen · ${formatSeenTime(device.firstSeen)}"

            addBlock(
                card,
                label(
                    firstSeenText,
                    11f,
                    mutedText,
                    true
                ),
                8
            )
        }

        val portSummary = when {
            !device.portsChecked -> {
                "Ports not checked yet"
            }

            device.openPorts.isEmpty() -> {
                "No open ports among those checked"
            }

            else -> {
                device.openPorts
                    .sorted()
                    .joinToString("  ·  ") { port ->
                        "$port/${getServiceName(port)}"
                    }
            }
        }

        addBlock(
            card,
            label(portSummary, 12f, lime, true),
            12
        )

        val inspectButton = action("Inspect device  →")

        inspectButton.setOnClickListener {
            // Retrieve the latest result for this IP address.
            val currentDevice = devices[device.ipAddress]

            if (currentDevice != null) {
                showDeviceDetails(currentDevice)
            }
        }

        addBlock(card, inspectButton, 14)

        cards[device.ipAddress] = card

        deviceContainer.addView(
            card,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply {
                topMargin = dp(12)
            }
        )

        updateMetrics()
    }

    // ========================================================
    // DEVICE INSPECTOR
    // ========================================================

    private fun showDeviceDetails(device: NetworkDevice) {
        val content = column().apply {
            setPadding(dp(22), dp(12), dp(22), dp(12))
        }

        // Local helper for a title followed by selectable text.
        fun field(title: String, value: String) {
            addBlock(
                content,
                label(title, 10f, mutedText, true),
                18
            )

            val valueLabel = label(
                value,
                14f,
                primaryText,
                true
            ).apply {
                setTextIsSelectable(true)
            }

            addBlock(content, valueLabel, 7)
        }

        val status = when {
            device.isThisDevice -> "THIS DEVICE"
            device.isNewDevice -> "NEW DEVICE"
            else -> "KNOWN DEVICE"
        }

        field("STATUS", status)
        field("IP ADDRESS", device.ipAddress)
        field("HOSTNAME", device.hostname)
        field("MAC ADDRESS", device.macAddress)
        field("DEVICE TYPE · ESTIMATED", device.deviceType)

        if (device.firstSeen > 0L) {
            field(
                "FIRST SEEN",
                formatFullTime(device.firstSeen)
            )
        }

        if (device.lastSeen > 0L) {
            field(
                "LAST SEEN",
                formatFullTime(device.lastSeen)
            )
        }

        val portDetails =
            if (device.openPorts.isEmpty()) {
                "None detected among checked ports"
            } else {
                device.openPorts
                    .sorted()
                    .joinToString("\n") { port ->
                        "$port  /  ${getServiceName(port)}"
                    }
            }

        field("OPEN TCP PORTS", portDetails)

        val webUrl = getWebInterfaceUrl(device)

        if (webUrl != null) {
            field("WEB INTERFACE", webUrl)

            val webButton = action(
                "Open Web Interface  →",
                true
            )

            webButton.setOnClickListener {
                openWebInterface(device)
            }

            addBlock(content, webButton, 20)
        }

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

        dialog.getButton(AlertDialog.BUTTON_POSITIVE)
            .setTextColor(lime)
    }

    // ========================================================
    // TIME FORMATTING AND SERVICE NAMES
    // ========================================================

    private fun formatSeenTime(time: Long): String {
        val elapsed = System.currentTimeMillis() - time

        return when {
            elapsed < 60_000L -> {
                "Just now"
            }

            elapsed < 3_600_000L -> {
                "${elapsed / 60_000L} min ago"
            }

            elapsed < 86_400_000L -> {
                SimpleDateFormat(
                    "h:mm a",
                    Locale.getDefault()
                ).format(Date(time))
            }

            else -> {
                SimpleDateFormat(
                    "MMM d, h:mm a",
                    Locale.getDefault()
                ).format(Date(time))
            }
        }
    }

    private fun formatFullTime(time: Long): String {
        val formatter = SimpleDateFormat(
            "MMM d, yyyy · h:mm:ss a",
            Locale.getDefault()
        )

        return formatter.format(Date(time))
    }

    /**
     * Conventional service names for the scanned ports.
     *
     * The actual service may differ; no protocol identification
     * is performed by this scanner.
     */
    private fun getServiceName(port: Int): String {
        return when (port) {
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
    }

    // ========================================================
    // SCAN COMPLETION AND CANCELLATION
    // ========================================================

    private fun finishScan(scan: ScanSession) {
        // Ignore callbacks from a scan that is no longer active.
        if (session !== scan) {
            return
        }

        ui.removeCallbacks(networkMonitor)
        session = null

        setScanAppearance(false, "COMPLETE")

        progressScan.visibility = View.GONE
        btnScan.text = "Scan again  →"

        val peerCount = devices.values.count { device ->
            !device.isThisDevice
        }

        val newDeviceCount = devices.values.count { device ->
            device.isNewDevice && !device.isThisDevice
        }

        if (!baselineEstablished) {
            baselineEstablished = true

            preferences.edit()
                .putBoolean(PREF_BASELINE, true)
                .apply()

            for (device in devices.values) {
                device.isNewDevice = false
            }

            txtResultNote.text =
                "Baseline established · future scans will flag new devices"

            txtStatus.text =
                "Baseline complete - $peerCount other devices remembered"

            // Snapshot the collection before rebuilding its cards.
            val baselineDevices = devices.values.toList()

            for (device in baselineDevices) {
                displayDevice(device)
            }

            return
        }

        txtResultNote.text =
            if (newDeviceCount > 0) {
                "Scan complete · $newDeviceCount new device(s) detected"
            } else {
                "Scan complete · no new devices detected"
            }

        txtStatus.text =
            "Scan complete - $peerCount other devices responded"
    }

    private fun stopScan(message: String) {
        val currentScan = session ?: return

        // Clear the active session first so queued results are ignored.
        session = null
        currentScan.stop()

        ui.removeCallbacks(networkMonitor)

        setScanAppearance(false, "STOPPED")

        progressScan.visibility = View.GONE
        btnScan.text = "Scan again  →"
        btnScan.isEnabled = true

        txtStatus.text = message
        txtResultNote.text = "Partial scan results"
    }

    // ========================================================
    // ACTIVITY CLEANUP
    // ========================================================

    override fun onStop() {
        inputDialog?.dismiss()
        inputDialog = null

        // Scanning is foreground-only in this implementation.
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