#!/bin/sh
# OkHttp 5.5.1's HTTP/2 WindowCounter.update writes both counts before its last check(this.acknowledged <= this.total):
# an update acknowledging more than was consumed throws IllegalStateException and leaves the counter holding it.
# Compiles the release's own file with kotlinc and runs it.
#   sh research/realworld/repro/okhttp-windowcounter.sh          (kotlinc and a JDK on the PATH, or $KOTLIN_HOME)
set -e
KOTLINC=${KOTLIN_HOME:+$KOTLIN_HOME/bin/}kotlinc
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
curl -sfL -o "$W/WindowCounter.kt" https://raw.githubusercontent.com/square/okhttp/parent-5.5.1/okhttp/src/commonJvmAndroid/kotlin/okhttp3/internal/http2/flowcontrol/WindowCounter.kt
cat > "$W/Main.kt" <<'KT'
import okhttp3.internal.http2.flowcontrol.WindowCounter
fun main() {
  val w = WindowCounter(streamId = 1)
  try { w.update(acknowledged = 3) } catch (e: IllegalStateException) { println("update(acknowledged = 3) threw: $e") }
  println("after it: $w")
}
KT
"$KOTLINC" -nowarn "$W/WindowCounter.kt" "$W/Main.kt" -include-runtime -d "$W/r.jar" 2>/dev/null
${JAVA_HOME:+$JAVA_HOME/bin/}java -jar "$W/r.jar"
