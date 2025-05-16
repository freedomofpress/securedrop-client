---
name: Release
about: Create a tracking ticket for a SecureDrop Client release

---

This issue tracks the SecureDrop Client release [version]. It will be organized by:

- Release Manager:
- Deputy Release Manager:

This release includes the following changes:
- [high level summary of changes]

SecureDrop maintainers and testers: As you QA this release, please report back your testing results as comments on this ticket. File GitHub issues for any problems found, tag them "QA: Release", and associate them with the release milestone for tracking (or ask a maintainer to do so).

## Test plan

[Make sure to include the version(s) of the server that need to be tested against. If the release is being coordinated with a server release, specify rc versions of the server that need to be tested and release order. Once completed, insert or link to a test plan here. It can be left out until then.]

- [ ] Pseudolocale (`LANG=en_XA`) QA per <https://github.com/freedomofpress/securedrop-workstation/wiki/Workstation-Acceptance-Tests#internationalization-reference>

## Release tasks

The following checklist is derived from [the developer documentation](https://developers.securedrop.org/en/latest/workstation_release_management.html).

- [ ] Check if there are any security bug fixes waiting to be pulled into the RC
- [ ] Check if there are any translations:
    - [ ] [pending merge](https://github.com/freedomofpress/securedrop-client/pulls/weblate-fpf) into `main`
    - [ ] pending inclusion as a supported language in [`MANIFEST.in`](https://github.com/freedomofpress/securedrop-client/blob/main/MANIFEST.in)
- [ ] Update changelog
- [ ] Create test plan
- [ ] Build and deploy the package to `apt-test`
- [ ] Begin formal QA (and iterate until suitable release candidate)
- [ ] Build production package
- [ ] Sign production package
- [ ] Perform final pre-flight testing using `apt-qa.freedom.press`
  - [ ] **Localization:** In a `sd-app`, the locale to a [supported language](https://github.com/freedomofpress/securedrop-client/blob/main/client/MANIFEST.in#L32-L34) (e.g.: `sudo dpkg-reconfigure locales` and select `pt_PT.utf-8` and apply.). Run the Client, and confirm that the application is translated.
- [ ] Publish production package
- [ ] Publicize release via support channels

# Post-release Tasks
- [ ] Run the updater on a production setup once packages are live, and conduct a smoketest (successful updater run, and basic functionality if updating client packages).
- [ ] Backport changelog commit(s) with `git cherry-pick -x` from the release branch into the main development branch, and sign the commit(s).
- [ ] Run the `./update_version.sh` script to bump the version on main to the next minor version’s rc1. Open a PR with these commits; this PR can close the release tracking issue.
