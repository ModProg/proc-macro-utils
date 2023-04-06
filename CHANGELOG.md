# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- ## [Unreleased] -->

## [0.5.2] - 2023-04-06
### Fixed
- `Parser::peek_n()` always returned `None`
- `Parser::next_{token}` did not work correctly because of `peek_n`

## [0.5.1] - 2023-03-02
### Fixed
- `Parser::next_string()` did not consume token

## [0.5.0] - 2023-03-01
### Added
- Parser for parsing simple rust structures
- `assert_tokens!` macro
- `TokenTreeExt::into_<token>()` functions 
- `Delimited` trait for accessing `TokenTree::Group`

### Changed
- **Breaking Change** `TokenTreeExt::<token>()` now return references

[unreleased]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.2...HEAD
[0.5.2]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.1...v0.5.2
[0.5.1]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.4.0...v0.5.0
