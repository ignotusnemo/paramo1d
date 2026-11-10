# Android storage check

This fixture runs the application's `SecureStore` and native backup implementation under the separate package `org.parano1d.courier.storagecheck`. Android assigns it its own UID, private directory and Keystore namespace. The fixture identity is deterministic and unfunded.

The create stage checks the encrypted local archive, recovery after an interrupted write, rejection of a modified archive, portable backup restoration, and rejection of a wrong password or modified backup. The reopen stage checks the local archive and portable backup after a process restart.

Build the main Android native library first, then run from the repository root with the Android SDK and JDK configured:

```sh
gradle --no-daemon -p android/storage-check assembleDebug
adb install -r -t android/storage-check/build/outputs/apk/debug/storage-check-debug.apk
adb shell am instrument -w -e stage create org.parano1d.courier.storagecheck/org.parano1d.courier.StorageCheck
adb shell am force-stop org.parano1d.courier.storagecheck
adb shell am instrument -w -e stage reopen org.parano1d.courier.storagecheck/org.parano1d.courier.StorageCheck
```

Both runs must return `status=passed` and instrumentation code `-1`. Test output contains the stage and assertion count. The fixture package can then be removed:

```sh
adb uninstall org.parano1d.courier.storagecheck
```

The test project copies the two production Java files during its build and links the same `libparamo1d.so` as the app. Its manifest requests no network permission.
