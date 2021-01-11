workspace(name = "poe")

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "io_bazel_rules_rust",
    # commit = "f32695dcd02d9a19e42b9eb7f29a24a8ceb2b858",
    branch = "master",
    remote = "https://github.com/bazelbuild/rules_rust.git",
)

load("@io_bazel_rules_rust//rust:repositories.bzl", "rust_repositories")

rust_repositories(version = "nightly", iso_date = "2020-10-05", edition="2018")
