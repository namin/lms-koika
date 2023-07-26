# Managing `lms-clean`

To ease dependency management, we build `lms-clean` from `vendor/lms-clean`,
which contains our fork of that repository. The easiest way to sync this fork
with [upstream](https://github.com/TiarkRompf/lms-clean) requires
[`git subrepo`](https://github.com/ingydotnet/git-subrepo) -- from a clean
working tree, simply run `git subrepo pull` from the project root. This will
pull from upstream and announce merge conflicts as necessary.

Pushing changes from this fork back upstream is a little more involved. First,
fork `lms-clean` and add a remote as follows:

```
$ git remote add <my-lms-clean> <my-lms-clean-url>
```

Now, changes can be pushed to your fork of `lms-clean` via

```
$ git subrepo push -r <my-lms-clean> [<optional branch>]
```

Note that you can also pull changes from this remote similarly via

```
$ git subrepo pull -r <my-lms-clean> [<optional branch>]
```
