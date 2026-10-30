// swift-tools-version:5.9
// The extractor's Swift reader (core/extract-swift.ts builds it once per version of its source): one executable on
// swift-syntax's parser, pinned. Where the toolchain ships SwiftSyntax for its macros (lib/swift/host), the front end
// compiles main.swift against that instead, in seconds; this package is the fallback (minutes, once).
import PackageDescription

let package = Package(
  name: "gdp-swiftreader",
  dependencies: [.package(url: "https://github.com/swiftlang/swift-syntax.git", exact: "603.0.2")],
  targets: [.executableTarget(name: "gdp-swiftreader", dependencies: [
    .product(name: "SwiftSyntax", package: "swift-syntax"), .product(name: "SwiftParser", package: "swift-syntax"),
    .product(name: "SwiftOperators", package: "swift-syntax")])]
)
