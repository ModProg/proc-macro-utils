# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.5.0] - 2023-03-01
### Added
- Parser for parsing simple rust structures
- `assert_tokens!` macro
- `TokenTreeExt::into_<token>()` functions 
- `Delimited` trait for accessing `TokenTree::Group`

### Changed
- **Breaking Change** `TokenTreeExt::<token>()` now return references

[unreleased]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.0...HEAD
[0.5.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.4.0...v0.5.0
