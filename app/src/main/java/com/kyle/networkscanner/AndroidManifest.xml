package com.kyle.networkscanner

import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.net.ConnectivityManager
import android.net.Network
import android.net.NetworkCapabilities
import android.os.Build
import androidx.core.app.NotificationCompat
import androidx.core.app.NotificationManagerCompat
import androidx.core.content.ContextCompat
import androidx.work.*
import java.net.ConnectException
import java.net.Inet4Address
import java.net.InetAddress
import java.net.InetSocketAddress
import java.net.Socket
import java.util.concurrent.Callable
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit

class BackgroundDeviceWorker(
    context: Context,
    parameters: WorkerParameters
) : Worker(context, parameters) {

    private data class Lan(
        val network: Network,
        val localIp: String,
        val localNumber: Long,
        val prefix: Int
    )

    private data class KnownDevice(
        val ip: String,
        var hostname: String,
        var mac: String,
        var type: String,
        var firstSeen: Long,
        var lastSeen: Long
    )

    companion object {
        private const val WORK_NAME = "background_device_monitor"
        private const val PREFS = "net_scanner_devices"
        private const val PREF_BASELINE = "baseline_established"
        private const val PREF_DEVICES = "known_devices"
        private const val CHANNEL_ID = "new_device_alerts"
        private const val TIMEOUT = 250

        private val PORTS = intArrayOf(
            22, 53, 80, 139, 443, 445,
            554, 631, 8008, 8009, 8080, 9100
        )

        fun schedule(context: Context) {
            val constraints = Constraints.Builder()
                .setRequiredNetworkType(NetworkType.CONNECTED)
                .setRequiresBatteryNotLow(true)
                .build()

            val request = PeriodicWorkRequest.Builder(
                BackgroundDeviceWorker::class.java,
                15,
                TimeUnit.MINUTES
            )
                .setConstraints(constraints)
                .build()

            WorkManager.getInstance(context)
                .enqueueUniquePeriodicWork(
                    WORK_NAME,
                    ExistingPeriodicWorkPolicy.KEEP,
                    request
                )
        }

        fun stop(context: Context) {
            WorkManager.getInstance(context)
                .cancelUniqueWork(WORK_NAME)
        }
    }

    override fun doWork(): Result {
        val prefs = applicationContext.getSharedPreferences(
            PREFS,
            Context.MODE_PRIVATE
        )

        if (!prefs.getBoolean(PREF_BASELINE, false)) {
            return Result.success()
        }

        val lan = findLan() ?: return Result.success()
        val known = loadKnown(
            prefs.getStringSet(PREF_DEVICES, emptySet())
        )

        val range = scanRange(lan)
        val pool = Executors.newFixedThreadPool(40)

        return try {
            val tasks = range
                .filter { ipText(it) != lan.localIp }
                .map { number ->
                    Callable<Pair<String, List<Int>>?> {
                        if (isStopped) {
                            null
                        } else {
                            val ip = ipText(number)
                            val ports = scanHost(ip, lan.network)

                            if (ports == null) null
                            else Pair(ip, ports)
                        }
                    }
                }

            val results = pool.invokeAll(tasks).mapNotNull {
                try {
                    it.get()
                } catch (_: Exception) {
                    null
                }
            }

            val now = System.currentTimeMillis()

            for ((ip, ports) in results) {
                val previous = known[ip]

                if (previous == null) {
                    val type = deviceType(ports)

                    known[ip] = KnownDevice(
                        ip = ip,
                        hostname = "Unknown Device",
                        mac = "Unavailable",
                        type = type,
                        firstSeen = now,
                        lastSeen = now
                    )

                    notifyNewDevice(ip, type, ports)
                } else {
                    previous.lastSeen = now
                }
            }

            saveKnown(prefs, known)
            Result.success()
        } catch (_: Exception) {
            Result.retry()
        } finally {
            pool.shutdownNow()
        }
    }

    private fun findLan(): Lan? {
        val manager = applicationContext.getSystemService(
            Context.CONNECTIVITY_SERVICE
        ) as ConnectivityManager

        for (network in manager.allNetworks) {
            val capabilities =
                manager.getNetworkCapabilities(network) ?: continue

            val wifi = capabilities.hasTransport(
                NetworkCapabilities.TRANSPORT_WIFI
            )

            val ethernet = capabilities.hasTransport(
                NetworkCapabilities.TRANSPORT_ETHERNET
            )

            val vpn = capabilities.hasTransport(
                NetworkCapabilities.TRANSPORT_VPN
            )

            if ((!wifi && !ethernet) || vpn) continue

            val properties =
                manager.getLinkProperties(network) ?: continue

            for (linkAddress in properties.linkAddresses) {
                val address =
                    linkAddress.address as? Inet4Address ?: continue

                if (
                    address.isLoopbackAddress ||
                    address.isAnyLocalAddress ||
                    address.isMulticastAddress
                ) continue

                val ip = address.hostAddress ?: continue

                return Lan(
                    network = network,
                    localIp = ip,
                    localNumber = ipNumber(address),
                    prefix = linkAddress.prefixLength
                )
            }
        }

        return null
    }

    private fun scanRange(lan: Lan): LongRange {
        val mask = if (lan.prefix == 0) {
            0L
        } else {
            (0xFFFFFFFFL shl (32 - lan.prefix)) and 0xFFFFFFFFL
        }

        val network = lan.localNumber and mask
        val broadcast = network or (mask xor 0xFFFFFFFFL)

        var first =
            if (lan.prefix >= 31) network else network + 1

        var last =
            if (lan.prefix >= 31) broadcast else broadcast - 1

        // Limit large networks to this phone's local /24 block.
        if (last - first + 1 > 254) {
            val localBlock = lan.localNumber and 0xFFFFFF00L
            first = maxOf(first, localBlock + 1)
            last = minOf(last, localBlock + 254)
        }

        return first..last
    }

    private fun scanHost(
        ip: String,
        network: Network
    ): List<Int>? {
        val address = try {
            InetAddress.getByName(ip)
        } catch (_: Exception) {
            return null
        }

        var responded = false
        val openPorts = mutableListOf<Int>()

        for (port in PORTS) {
            if (isStopped) return null

            var socket: Socket? = null

            try {
                socket = network.socketFactory.createSocket()

                socket.connect(
                    InetSocketAddress(address, port),
                    TIMEOUT
                )

                responded = true
                openPorts.add(port)
            } catch (error: Exception) {
                if (wasRefused(error)) responded = true
            } finally {
                try {
                    socket?.close()
                } catch (_: Exception) {
                }
            }
        }

        return if (responded) openPorts else null
    }

    private fun wasRefused(error: Throwable): Boolean {
        var cause: Throwable? = error

        while (cause != null) {
            if (
                cause is ConnectException ||
                cause.message?.contains(
                    "refused",
                    ignoreCase = true
                ) == true
            ) {
                return true
            }

            cause = cause.cause
        }

        return false
    }

    private fun deviceType(ports: List<Int>): String {
        return when {
            8008 in ports || 8009 in ports ->
                "Google Cast Device"

            9100 in ports || 631 in ports ->
                "Printer"

            554 in ports ->
                "Camera / Media Device"

            445 in ports || 139 in ports ->
                "Computer / NAS"

            53 in ports &&
                (80 in ports || 443 in ports) ->
                "Router / Network Device"

            22 in ports ->
                "Computer / Network Device"

            80 in ports ||
                443 in ports ||
                8080 in ports ->
                "Web / Network Device"

            else ->
                "Unknown Device"
        }
    }

    private fun loadKnown(
        records: Set<String>?
    ): MutableMap<String, KnownDevice> {
        val devices =
            linkedMapOf<String, KnownDevice>()

        for (record in records ?: emptySet()) {
            val parts = record.split("|")

            if (parts.size < 6) continue

            val firstSeen =
                parts[4].toLongOrNull() ?: continue

            val lastSeen =
                parts[5].toLongOrNull() ?: firstSeen

            devices[parts[0]] = KnownDevice(
                ip = parts[0],
                hostname = parts[1],
                mac = parts[2],
                type = parts[3],
                firstSeen = firstSeen,
                lastSeen = lastSeen
            )
        }

        return devices
    }

    private fun saveKnown(
        prefs: SharedPreferences,
        devices: Map<String, KnownDevice>
    ) {
        val records = devices.values.map {
            "${it.ip}|${clean(it.hostname)}|" +
                "${clean(it.mac)}|${clean(it.type)}|" +
                "${it.firstSeen}|${it.lastSeen}"
        }.toSet()

        prefs.edit()
            .putStringSet(PREF_DEVICES, records)
            .apply()
    }

    private fun clean(value: String): String {
        return value.replace("|", " ")
    }

    private fun notifyNewDevice(
        ip: String,
        type: String,
        ports: List<Int>
    ) {
        val notificationPermission =
            "android.permission.POST_NOTIFICATIONS"

        if (
            Build.VERSION.SDK_INT >= 33 &&
            ContextCompat.checkSelfPermission(
                applicationContext,
                notificationPermission
            ) != PackageManager.PERMISSION_GRANTED
        ) {
            return
        }

        createChannel()

        val intent = Intent(
            applicationContext,
            MainActivity::class.java
        ).apply {
            flags = Intent.FLAG_ACTIVITY_NEW_TASK or
                Intent.FLAG_ACTIVITY_CLEAR_TOP
        }

        val pendingIntent = PendingIntent.getActivity(
            applicationContext,
            0,
            intent,
            PendingIntent.FLAG_UPDATE_CURRENT or
                PendingIntent.FLAG_IMMUTABLE
        )

        val portText = if (ports.isEmpty()) {
            "No monitored open ports detected"
        } else {
            "Open ports: ${ports.joinToString()}"
        }

        val message =
            "A new device appeared on your network.\n\n" +
                "IP: $ip\n" +
                "Type: $type\n" +
                portText

        val notification = NotificationCompat.Builder(
            applicationContext,
            CHANNEL_ID
        )
            .setSmallIcon(
                android.R.drawable.stat_notify_sync
            )
            .setContentTitle("New device detected")
            .setContentText("$ip · $type")
            .setStyle(
                NotificationCompat.BigTextStyle()
                    .bigText(message)
            )
            .setContentIntent(pendingIntent)
            .setPriority(NotificationCompat.PRIORITY_HIGH)
            .setAutoCancel(true)
            .build()

        try {
            NotificationManagerCompat
                .from(applicationContext)
                .notify(
                    ip.hashCode() and Int.MAX_VALUE,
                    notification
                )
        } catch (_: SecurityException) {
        }
    }

    private fun createChannel() {
        if (Build.VERSION.SDK_INT < 26) return

        val manager = applicationContext.getSystemService(
            Context.NOTIFICATION_SERVICE
        ) as NotificationManager

        val channel = NotificationChannel(
            CHANNEL_ID,
            "New Device Alerts",
            NotificationManager.IMPORTANCE_HIGH
        ).apply {
            description =
                "Alerts when new network devices are detected"

            enableVibration(true)
        }

        manager.createNotificationChannel(channel)
    }

    private fun ipNumber(address: Inet4Address): Long {
        var result = 0L

        for (byte in address.address) {
            result =
                (result shl 8) or
                    (byte.toLong() and 255L)
        }

        return result
    }

    private fun ipText(value: Long): String {
        return "${value shr 24 and 255}." +
            "${value shr 16 and 255}." +
            "${value shr 8 and 255}." +
            "${value and 255}"
    }
}