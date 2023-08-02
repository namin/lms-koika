# Managing `lms-clean`

To ease dependency management, we build `lms-clean` from `vendor/lms-clean`,
which contains our fork of that repository. This is managed by `git subtree`,
which is bundled with git since version 1.7.11.

## Quickstart

From the root of the repo:

To pull from upstream:
```
$ git subtree pull --prefix vendor/lms-clean https://github.com/TiarkRompf/lms-clean master --squash
```

To push to a fork:
```
$ git subtree push --prefix vendor/lms-clean <my-fork-url> <branch>
```

To avoid needing to type out URLs every time, they can be added as remotes:

```
$ git remote add lms-clean-master https://github.com/TiarkRompf/lms-clean
```

and now `lms-clean-master` can be used in place of a URL in the above commands.

## Miscellanea

- To minimize issues with merging, `vendor/lms-clean` should be up to date with
  `master` before pushing. Rebases are known to cause issues if it causes the
  history of `lms-koika` to diverge from the most recent push.

- If getting the error `refusing to merge unrelated histories` when pulling,
  make sure not to forget the `--squash` option.

- The commits pushed back to `lms-clean` (or forks thereof) will be all commits
  touching `vendor/lms-clean` in the history of this repo since the previous
  push/pull from that remote. This means that, if there are commits that change
  both `lms-clean` and `lms-koika`, the commit messages may not be immediately
  relevant. These can be resolved on the fork, or avoided entirely by not
  making such component-spanning commits.
