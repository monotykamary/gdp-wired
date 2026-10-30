#!/bin/sh
# grpc-java 1.85.1's retry throttle (RetriableStream.Throttle) past Integer.MAX_VALUE: ServiceConfigUtil.getThrottlePolicy
# checks only maxTokens > 0, and at 2,147,484 tokens or more maxTokens (1000 times them, a float cast to int) saturates at
# Integer.MAX_VALUE; one qualified failure then one success with a token ratio over 1 overflows currentCount + tokenRatio,
# and the count the comment says "will always be between 0 and maxTokens" goes negative. Runs the release's own jar.
#   sh research/realworld/repro/grpc-throttle-overflow.sh        (a JDK 17 or later: $JAVA_HOME or java on the PATH)
set -e
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
curl -sfL -o "$W/grpc-core.jar" https://repo1.maven.org/maven2/io/grpc/grpc-core/1.85.1/grpc-core-1.85.1.jar
cat > "$W/Repro.java" <<'JAVA'
import java.lang.reflect.*;
import java.util.concurrent.atomic.AtomicInteger;
public class Repro {
  public static void main(String[] a) throws Exception {
    Class<?> c = Class.forName("io.grpc.internal.RetriableStream$Throttle");
    Constructor<?> k = c.getDeclaredConstructor(float.class, float.class); k.setAccessible(true);
    Object t = k.newInstance(2147484f, 2f);
    Field f = c.getDeclaredField("tokenCount"); f.setAccessible(true);
    Field max = c.getDeclaredField("maxTokens"); max.setAccessible(true);
    Method fail = c.getDeclaredMethod("onQualifiedFailureThenCheckIsAboveThreshold"); fail.setAccessible(true);
    Method ok = c.getDeclaredMethod("onSuccess"); ok.setAccessible(true);
    System.out.println("maxTokens " + max.get(t) + ", start " + f.get(t));
    fail.invoke(t); System.out.println("after a qualified failure: " + f.get(t));
    ok.invoke(t); System.out.println("after a success: " + f.get(t) + (((AtomicInteger) f.get(t)).get() < 0 ? "  (below 0: the documented invariant broken)" : ""));
    fail.invoke(t); System.out.println("after another failure: " + f.get(t));
  }
}
JAVA
"$JAVA" -cp "$W/grpc-core.jar" "$W/Repro.java"
