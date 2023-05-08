# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- `quote::ToTokens` implementation for `TokenParser` (`quote` is a new default feature).
- `peek_{token}` and `peek_n_{token}` to `TokenParser`.

### Changed
- **Breaking Change** Added const generic buffer size to `TokenParser`.
- **Breaking Change** `Peeker::peek` takes `&[TokenTree]` instead of `TokenParser`.
- **Breaking Change** `*_{delimiter}` returns `Group` instead of the contained stream.
  To get to the stream call `.stream()`
- `TokenParser` peeking supports `n` greater than stack buffer, allowing spilling to heap.
- Increased default `TokenParser` peek buffer to `6`.
- Marked parser functions as must_use.

## [0.6.0] - 2023-04-29
- `TokenParser::next_keyword(v)`

## [0.5.2] - 2023-04-06
### Fixed
- `TokenParser::peek_n()` always returned `None`
- `TokenParser::next_{token}` did not work correctly because of `peek_n`

## [0.5.1] - 2023-03-02
### Fixed
- `TokenParser::next_string()` did not consume token

## [0.5.0] - 2023-03-01
### Added
- `TokenParser` for parsing simple rust structures
- `assert_tokens!` macro
- `TokenTreeExt::into_<token>()` functions 
- `Delimited` trait for accessing `TokenTree::Group`

### Changed
- **Breaking Change** `TokenTreeExt::<token>()` now return references

[unreleased]: https://github.com/ModProg/proc-macro-utils/compare/v0.6.0...HEAD
[0.6.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.2...v0.6.0
[0.5.2]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.1...v0.5.2
[0.5.1]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.4.0...v0.5.0
