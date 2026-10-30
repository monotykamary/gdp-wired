# A JDK and Kotlin for the JVM front ends' jobs (core/extract-jvm.ts), once per container: Temurin 21 (Adoptium) and
# Kotlin 2.4.21's compiler (its lib/ has the PSI the Kotlin reader parses with and the standard library), unless the
# image has them. Source it (`. research/langs/jvm/jvm-setup.sh`): it exports JAVA_HOME and KOTLIN_HOME.
if [ -z "$JAVA_HOME" ] || [ ! -x "$JAVA_HOME/bin/javac" ]; then
  if [ ! -x /opt/jdk/bin/javac ]; then
    mkdir -p /opt/jdk && timeout -s KILL 300 sh -c 'curl -fsSL "https://api.adoptium.net/v3/binary/latest/21/ga/linux/x64/jdk/hotspot/normal/eclipse" | tar xz -C /opt/jdk --strip-components=1' || echo "jvm-setup: the JDK failed"
  fi
  export JAVA_HOME=/opt/jdk
fi
if [ -z "$KOTLIN_HOME" ] || [ ! -f "$KOTLIN_HOME/lib/kotlin-compiler.jar" ]; then
  if [ ! -f /opt/kotlinc/lib/kotlin-compiler.jar ]; then
    timeout -s KILL 300 sh -c 'curl -fsSL -o /tmp/kotlinc.zip https://github.com/JetBrains/kotlin/releases/download/v2.4.21/kotlin-compiler-2.4.21.zip && unzip -q -o /tmp/kotlinc.zip -d /opt && rm -f /tmp/kotlinc.zip' || echo "jvm-setup: kotlinc failed"
  fi
  export KOTLIN_HOME=/opt/kotlinc
fi
export PATH="$JAVA_HOME/bin:$KOTLIN_HOME/bin:$PATH"
"$JAVA_HOME/bin/javac" -version 2>&1; "$JAVA_HOME/bin/java" -cp "$KOTLIN_HOME/lib/kotlin-compiler.jar" org.jetbrains.kotlin.cli.jvm.K2JVMCompiler -version 2>&1 | head -1
