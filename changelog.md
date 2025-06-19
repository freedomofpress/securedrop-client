# Changelog

## 0.16.0

* Display detailed last update times for sources (#2447)
* Use a single typeface, Source Sans Pro, across the application (#2430)

### Dependencies
* Update Rust to 1.87.0 (#2458)
* Update setuptools to 78.1.1 (#2457)
* Update development dependencies (#2438, #2459, #2460)

## 0.15.0

This release vastly expands printer options by using IPP-over-USB to support most
AirPrint-capable printer with a USB port, in addition to switching to the modern
GTK print dialog. This release also adds progress bars to give users visual
feedback while a file is downloading.

* Initial support for IPP / driverless printing (#2332, #2434, #2433)
* Replace XPP with GTK-based print dialog (#2411)
* Display download progress for file downloads (#2327, #2428, #2427, #2426, #2424, #2329)
* Localization: Standardize on "drive" (versus "device") for USB export devices (#2251)
* Update translations from Weblate (#2322)

### Dependencies
* Upgrade to jinja2 3.1.6 for CVE-2025-27516 (#2410)
* Upgrade openssl from 0.10.66 to 0.10.70 (#2374)
* Upgrade openssl (RUSTSEC-2025-0022) and tokio (RUSTSEC-2025-0023) (#2414)
* Upgrade Rust toolchain to 1.84.1 (#2379)
* Upgrade url to v2.5.4 for CVE-2024-12224 #2328
* Upgrade six to 1.16.0 #2387
* Development dependencies (#2337, #2326, #2338, #2320, #2401, #2311, #2403,
#2415, #2336, #2340, #2357, #2397)

### Internal and Development
* Lint GitHub Actions workflows with zizmor (#2331)
* Remove outdated setuptools install_requires and python_requires (#2356)
* Remove quotation marks around .desktop entry name (#2086)
* SDK: Configure custom proxy VM via QubesDB/env; update docs (#2236)
* Enable development on macOS arm64 (#2334)
* Enable ruff's flake8-bugbear ruleset (#2341)
* Fail tests if the signing key will expire soon (#2390)
* Build: replicate securedrop's verification of head, tag, and working tree (#2431)
* Chore: ignore CVE-2024-56201 in jinja2 (#2376)
* Chore: update build requirements (#2420)

## 0.14.1

This release contains fixes for two security issues; please see our advisory for more details.

* Security fixes:
  * Prevent path manipulation/traversal attacks in SDK (CVE-2025-24888)
  * Don't send source VM name to sd-log (CVE-2025-24889)

* Miscellaneous:
  * Update year in messages.pot

## 0.14.0

* Add support for selecting and deleting multiple sources (#2208, #2188, #2230, #2252, #2293, #2299, #2300)
* Use builtin `venv` module instead of `virtualenv` (#2246)
* Improve logging of API failures (#2245)
* Improve client keyboard shortcuts handling (#2209)
* Fix client crash when a source with an in-progress download is deleted (#2217)
* Improve exception handling for download failures (#2275, #2276)
* Add French language support (#2283)
* Updated multiple dependencies (#2253, #2267, #2214, #2210, #2211)

* Internal and development
  * Switch securedrop-client package Architecture to "any" (#2178)
  * Have `run.sh` automatically emit full debug logs (#2198)
  * Have `make build-debs` print tag signature, if any (#2205)
  * Upgrade Rust toolchain to 1.81.0 (#2215)
  * Fixes to SD test cassettes (#2225)
  * Re-enable `ruff` for files in proxy/ (#2234)
  * Don't have CI cancel GitHub merge queue jobs (#2235)
  * Updated multiple dependencies (#2280, #2181, #2183)

## 0.13.2

* Don't let Range header persist into other requests (#2195)
* Have BaseErrors trigger DownloadDecryptionException in download flow (#2196)

## 0.13.1

* Ensure accurate mimetype detection of Office files, add additional sample files to integration tests (#2184)
* Support direct printing of image types supported by `cups` (#2174)
* Broaden printing support to all filetypes supported by LibreOffice (#2166)
* Display an error message if user tries to print an unprintable file type (#2166)
* Use single PrintDialog GUI element for all print actions (#2143)
* Remove unused `_from_string` methods from SDK (#2144)
* Update build toolchain and `setuptools` for CVE-2024-6345 (#2136, [securedrop-builder#501](https://github.com/freedomofpress/securedrop-builder/pull/501))
* Update `ruff` to 0.5.4 (#2138)

## 0.12.0

* Support viewing .heic and .avif files (#2110)
* Fix printing of Office documents requiring conversion to PDF (#2119)
* Show error details on Error screen of Export Wizard (#2098)
* Improve Export Wizard handling of button presses (#1926)
* Add hover state and animation to Print dialog buttons (#2125)
* Upgrade `openssl` Rust crate to 0.10.66 for RUSTSEC-2024-0357 (#2131)


## 0.11.0

This is the first release solely targeting Debian Bookworm. New features in the securedrop-client codebases will be available on Bookworm and Qubes 4.2 only.

* Support Qubes 4.2 and Debian Bookworm, drop 4.1 and Bullseye support (#1958)
* Automatically resume failed downloads (#2006)
* Update AppArmor `__pycache__` rules for Python 3.11 (#2000, #2010)
* Implement proxy v2 in Rust (#1718, #2017, #2031, #2039, #2015)
* Make sd-proxy VM disposable (#2033)
* Update release signing key expiry date to May 2027 (#2036)
* Allow nautilus to have RWX memory (#2060)
* Fix print preflight status check (#2102)
* Open `.webm` videos in Totem (#2106)

* Provisioning:
  * Install debian package requirements via sdw-config metapackage (#1957, #1967)
  * Provision deb822-style apt sources list (#1952)
  * Use QubesDB to configure VM-specific settings (#1883, #2034)
  * Use systemd and Qubes services to conditionally provision VMs (#1677, #2033)
  * Configure Journalist Interface auth credentials via QubesDB (#2032, #2051, #2056, #2058)
  * Use bash for all Debian packaging scripts (#1927)

* Internal and development:
  * Remove the pre-commit hook for make check-strings (#1896)
  * Display package hashes after successful build (#1898)
  * Exclude client version string from Project-Id-Version of .pot files (#1915)
  * Exclude root project .venv from bandit (#1918)
  * Run tests as not-root (#1919)
  * Automatically collect package build log (#1923)
  * Use ruff for linting and formatting checks (#1885, #1944)
  * Push "nightly" after each merged PR (#1960)
  * Update readme to reference python3.11 (#1969)
  * Install xfce4-terminal in all VMs for debugging (#2013)
  * Exclude Babel header from i18n diff in make check-strings (#2054, #2065)
  * Reorganize securedrop-log code to clearly split server and client (#1677)
  * Clean up unused securedrop-log code (#2014, #2042)
  * Document architecture of securedrop-log component (#1995)
  * Update most development dependencies to their latest versions
  * Add QubesDB and locally built packages to piuparts (#2032, #2034)


## 0.10.1
* Fix printing of transcripts. (#1936)

## 0.10.0

This is the first release from the merged securedrop-client repository, which now
contains the securedrop-export, securedrop-log, securedrop-proxy and securedrop-sdk
codebases. See our [blog post](https://securedrop.org/news/consolidating-securedrop-workstations-git-repositories-to-make-development-easier/) for more details.
All components now use the same version number, previous changelogs can be found in each
component's subfolder.

* VeraCrypt-encrypted USB drives are now supported for export. (#1777, #1908)
* Don't ask for a passphrase if the device is already unlocked ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105), #1777)
* Ensure all print jobs have been fully enqueued ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105))
* Cleanup `metadata.json` from sd-devices after exporting ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105))
* Add status code and error for multiple attached devices ([securedrop-export#105](https://github.com/freedomofpress/securedrop-export/pull/105))
* Improve detail in error messages when exporting fails and log them (#1777)
* Add spinner and active state in "Insert Encrypted Drive" dialog (#1019, #1777)
* Consistently transition to "Ready to export" state (#990, #1777)
* Fix typos in messages (#1651)
* Fix homepage URL in setup.py (#1662)
* Remove obsolete gvfs-bin dependency from securedrop-workstation-viewer (#1842)
* Make files exported to USBs world readable (#1872, #1917)
* Update translations from Weblate (#1548, #1747)
* Add `.rtf` printing support ([securedrop-export#109](https://github.com/freedomofpress/securedrop-export/pull/109))

* Dependencies:
  * Update requests to 2.31.0
  * Update certifi to 2023.7.22
  * Update jinja2 to 3.1.3

* Internal and development:
  * Fix syntax of mypy comments (#1646)
  * Pull out string "transcript.txt" into a constant (#1658)
  * Restore workaround for segmentation faults in tests (#1656)
  * Auto-detect Wayland in run.sh developer environment (#1653)
  * Verify gettext machine objects (`.mo`s) are reproducible (#1666)
  * Migrate dependency management to poetry (#1671)
  * Enable dependabot for Python and GitHub Actions (#1768, #1782, #1824, #1830)
  * Move and refactor debian/ packaging files from securedrop-builder (#1741)
  * Use `--require-hashes` when installing dependencies during package build (#1792)
  * Lint `.desktop` files in CI (#1783)
  * Apply bandit and safety linting to all components in one place (#1814)
  * Add initial configuration for Rust components (#1817, #1818)
  * Standardize `make lint` in all components (#1841)
  * Move remaining CircleCI jobs over to GitHub Actions (#1841)
  * Apply black and isort formatting to all components in one place (#1860)
  * Add shellcheck linting (#1843)
  * Stop using deprecated pkg_resources (#1851)
  * Have CI run piuparts (#1844)
  * Use dh_apparmor for installing the profile (#1856)
  * Use setuptools.find_packages() in setup.py (#1873)
  * Parameterize sender_is_current_user in test instead of randomization (#1884)
  * Stop running client tests in parallel with pytest-xdist (#1881)
  * Run lintian on Debian packages (#1845)
  * Run CI as a non-root user. (#1919)
  * Remove __pycache__ folders from packages. (#1909)
  * Remove specific version from .pot files. (#1915)

# Pre-consolidation changelogs

Prior to December 2023, most Debian packages required by the SecureDrop Workstation had
their own dedicated Git repository. Version numbers were advanced individually, and
separate changelogs were maintained for each package.

For additional background on this monorepo consolidation, see our [January 2024 blog post](https://securedrop.org/news/consolidating-securedrop-workstations-git-repositories-to-make-development-easier/).

The changelogs for each component prior to the consolidation can be found below.

The `securedrop-sdk` was distributed as a Python package on PyPI. Its changelog is also
included.

## securedrop-client

### 0.9.0
* Add localisation for UI date formats (#1636)
* Add status bar showing sync refresh information (#1604, #1613)
* Update options to print and export source transcripts and full conversations (#1582, #1621, #1624, #1627, #1631)
* Update download timeouts to allow for variations in Tor network performance (#1635)
* Update and improve localization support (#1539, #1578, #1616, #1620)
* Improve reply handling (#1486)
* Update desktop entry to match freedesktop specifications (#1589, #1601)
* Fix error status returned on successful export (#1594)
* Fix handling of untrusted strings (#1559, #1560)
* Add `pt_PT` and `zh_Hans` as supported languages (#1531)
* (Dev) Refactor export code (#1541, #1524)
* (Dev) Add support for Debian Bookworm (#1554, #1555, #1565, #1576, #1623)
* (Dev) Update dependencies, safety checks, and exemptions (#1574, #1573, #1587, #1597, #1599, #1609, #1610, #1625)
* (Dev) Miscellaneous developer documentation updates (#1557, #1590, #1622)
* (Dev) Add PyQT5 type checking (#1611, #1619)
* (Dev) Improve MacOS development environment support (#1592, #1603)
* (Dev) Fix spelling errors (#1588)
* (Dev) Update CI and build process to reference new `securedrop-builder` repo (#1586)
* (Dev) Update project licence information (#1571)
* (Dev) Improve functional test stability (#1525)
* (Dev) Add CI job to verify testing and production dependencies are in sync (#1556)
* (Dev) Improve logical organization of CI jobs (#1546)
* (Dev) Remove support for Debian Buster (#1544)

### 0.8.1
* Add experimental support for a custom timeout that allows the SecureDrop Client to retrieve a larger number of sources (#1552)

### 0.8.0
* Drop historical versions of database schema (#1517)
* Replace "show/hide passphrase" widget with checkbox to increase accessibility (#1430)
* Remove enclosing directory when all submissions have been deleted for a source (#1475)
* Support Debian Bullseye (#1494, #1511, #1528)
* Support Qubes 4.1 (#1495, #1530)
* Allow translations to be enabled/disabled per language (#1497, #1527)
* Handle terminating threads cleanly (#1512, #1518, #1519)
* (Dev) Add tooling for visualizing the codebase (#1484)
* (Dev) Refactor export and print dialogs for maintainability (#1492, #1498, #1502, #1501)
* (Dev) Refactor signals according to Qt best practices (#1508)
* (Dev) Prevent intermittent tests suite errors (#1515)
* (Dev) Decouple database tests from models (#1517)
* (Dev) Support development on Debian Bullseye (#1496)

### 0.7.0
* Clear global mouse selection after login (#1477)
* Update securedrop-sdk from version 0.3.2 to 0.4.0 (#1466)
* Add journalist read receipts (#1417, #1449, #1471)
* Speed up deletion of local files and database records (#1432, #1458, #1468, #1473)
* Add feature to download all files from a single source (#1388, #1448)
* Always invalidate the user when logging out (#1454)
* Refactors around user actions (#1447, #1400)
* Developer dependency updates for Pillow and pip-tools (#1433)

### 0.6.0
* Speed up source deletion (#1386, #1415)
* Use /users endpoint for managing journalist accounts (#1397)
* UI fix to bottom margin in conversation view (#1391)
* (Dev) Refactors that break up the widgets module into smaller components (#1377-1383, #1390, #1393, #1394)
* (Dev) Use Debian Stable container images in CI (#1385)
* (Dev) New templates for creating different types of GitHub Issues (#1392)
* (Dev) Add localization testing task to the release GitHub Issue template (#1401)

### 0.5.1
* Fix Python symlink, which broke package in 0.5.0

### 0.5.0

* Speed up deletion of conversations (#1311)
* Add tooltips with journalist name for badges (#1327)
* Add keyboard shortcut to quit application (#1331)
* Allow tabbing to the "Use offline" button on login dialog (#1328)
* Clear login error message on successful login attempt (#1321)
* Support deletion of conversations (#1263)
* Speed up deletion of accounts and conversations (#1273)
* Update securedrop-sdk version to 0.3.0 (#1274)
* Tighten file permissions (#1256)
* Fix bug that exports twice on Enter (#1241)
* Scale left pane background image (#1210)

### 0.4.1

* Prevent path traversal in downloaded files (#1226)
* Scale source list, preview and conversation view on resize (#1211, #1206)
* (Dev) Add semgrep for static analysis, including an initial ruleset (#1226)
* (Dev) Remove obsolete MIME setup in run.sh (#1215)
* (Dev) Switch to using reproducibly built wheels (#1203)
* (Dev) Update development dependencies (#1208, #1222)
* (Docs) Incorporate Code of Conduct updates (#1216)

### 0.4.0

* Support read/unread and track who sees a file, message, or reply (#1165)
* No longer expire source test key (#1180)
* Restyle source widgets and source selection indicators (#1191)
* No longer maximize client window if it's already open on login (#1192)
* Update securedrop-sdk version to 0.2.0 (#1172)
* (Dev) update macOS development requirements (#1183)

### 0.3.0

* Add sender badge to replies (#1142)
* Elide source designations at lower width (#1145)
* Correctly display client maximum window size in Qubes (#1130)
* Preview only the most recent message/file/reply (#1131)
* Fix styling for reply decryption errors (#1151)
* Update reply sender during a sync (#1137)
* Update info about the current user during a sync (#1135)
* Fix foreign key for reply attribution (#1147, #1184)
* Add DB migration testing and update incorrect foreign keys (#1162)
* Update requests and urllib3 requirements (#1155)
* Disable client and vault config in VMs other than sd-app (#1153)
* Enforce AppArmor profile in postinst (#1159)
* Remove MIME type associations from package (#1160)
* (Dev) Move requirements file to new directory (#1128)
* (Dev) Make functional test cassettes work in any order (#1138)
* (Dev) No longer expire test key (#1180)
* (Docs) Remove recommendation to merge migrations (#1161)
* (Docs) Updated documentation for running tests (#1144)
* (Docs) Incorporate Code of Conduct updates (#1136)

### 0.2.1

* Reformat the code with black and isort (#1115)
* Support multi-source deletions in one sync (#1114)
* Support more screen resolutions (#1103)
* Move CSS strings to CSS files and add new CSS tests (#1082)
* Prevent addition of duplicated API jobs (#975)

### 0.2.0

* Improve error handling when conversation items fail to decrypt (#1059).
* Enable copy/paste in SpeechBubble (#1063).
* Clear clipboard after login (#1071).
* Disable context menu on SpeechBubble (#1065).
* Rely on SDK default for most requests (#1056).
* Increase metadata sync timeout (#1055).
* Minimize number of database queries during sync (#1037, #1036).
* Defer source key import until reply (#1035).
* Speed up update_replies (#1046).
* Download items for most recently active sources first (#1043).
* Align source name and preview (#1044).
* Align file name and print button (#1045).
* Add utils.chronometer for measuring block execution time (#1034).
* Log intended folders instead of empty strings (#1069).
* Use looping animation for metadata sync (#1057).
* Use securedrop-sdk version 0.1.0 (#1076).
* Update PyYAML to 5.3.1 (#1041).
* Use pytest fixtures for functional tests (#1067).
* Bugfix: Remove leading and trailing whitespace from messages (#1058).

### 0.1.6

* Fix truncation and alignment issues in conversation view (#1029).

### 0.1.5

* Update source list ordering when conversation is updated (#1013).
* Do not show tooltips on short strings (#1016).

### 0.1.4

* Use `--view-only` when opening files in a DVM, update `mimeapps.list` (#972).
* Add user icon to clickable area for logout (#976).
* Animate active state on frameless dialog boxes (#940).
* String updates to print/export dialogs (#968).
* Automatically resize status bar to width of error message string (#977).
* Clean up cleanup in run.sh (#949).
* Make `LoginDialog` a modal (#978).
* Make `ExportDialog`, `PrintDialog` modals (#970).
* Switch button order in `ExportDialog`, `PrintDialog` (#989).
* Focus passphrase field in `ExportDialog` (#994).
* Disable cancel button before exporting a file (#1011).
* Ensure logging does not log sensitive info (#965).
* Reset source pending status upon unexpected error when deleting sources (#979).
* Fix star hover state (#1003).
* No longer show drafts in preview snippets (#1002).
* No longer access source database object in snippet (#964).
* Resolve blocked UI on client start for a large number of sources (#944).
* Add functional tests (#788, #957, #983, #1001).
* Bug fix: Show pending deletion status right after deletion job enqueued (#955).
* Bug fix: Fix starring behavior (#952).
* Bug fix: Prevent duplicate file downloads at the UI level (#974).
* Bug fix: Stop selecting a source on sync (#981).
* Bug fix: Fix horizontal scrollbar in source list (#982).
* Bug fix: Update filesize after download and decryption (#969).
* Bug fix: Prevent tooltips on source preview labels (#1006).

### 0.1.3

* Update login UI messages (#903).
* Add pending deletion status (#911).
* Bug fix: Delete conversation in one place (#915).
* Bug fix: Ensure that we delete individual submissions on disk (#923).
* Bug fix: Ensure that sources are properly refreshed on sync (#916).
* Bug fix: Fix word wrap in source (#926).
* Bug fix: Preview oneline and no longer condense text (#931).
* Bug fix: Ensure correct StarToggleButton signal handler state (#933).
* Bug fix: Ensure StarToggleButton hover states honor offline status (#936).
* Bug fix: Fix conversation refresh and syncing (#937).
* Bug fix: Fix StarToggleButton hover leave (#941).
* Bug fix: Make sure snippet is updated on submission deletion (#942).
* Bug fix: Use the id of the widget, not the db object in get_current_source (#943).
* Update MarkupSafe to 1.1.1 (#925).

### 0.1.2

 * Update branding bar artwork (#871).
 * Remove "downloading file" message in sync area (#881).
 * Bug fix: Only force login when we're not already logged out (#884).
 * Bug fix: Retry source deletion jobs (#879).
 * Bug fix: Enter no longer closes print and export dialogs (#855).
 * Bug fix: Ensure that ReplyBox is updated after client gets source key (#864).
 * Bug fix: Ensure that we delete source collection when source is deleted (#866).
 * Bug fix: Ensure that we delete Python wrappers for deleted items (#887, #890, #898).

### 0.1.1

  * Implement export/print UI design and behavior (#666).
  * Update sync method names and message (#817).
  * Bug fix: Ensure replies are in order (#829).
  * Bug fix: Do not mark replies as failed if they time out (#819).
  * Bug fix: If source is deleted during sync, do not add its messages (#832).
  * Provide clear message in case of no keypair (#830).
  * Bug fix: Ensure messages word wrap (#838).
  * Show a short notifications when messages are about to download (#822).
  * Standardize connection errors (#823).
  * Bug fix: Fix reply succeeds but shows up as failed (#837).
  * Bug fix: Ensure UI updates if local copy of file is no longer available (#842).
  * Bug fix: Work around stylesheet issue causing replies to show as pending when confirmed (#831).

### 0.1.0

  * Update file download animation (#731).
  * Update conversation view inline (#688).
  * When token is invalid, user must log back in (#750).
  * Ensure UI stays responsive at all times when syncing with server (#733).
  * Update conversation view on login (#748).
  * Improve download file handling (#737).
  * Show warning if source has no public key (#759).
  * No longer sync after sending a reply (#722).
  * Update gui instead of sync when a file is missing (#724).
  * Revert usage of subprocess.check_output text parameter (#755).
  * Update obsolete original_filename usage in file_ready (#773).
  * Don't import source keys we already have (#749).
  * Make sync continuous (#739).
  * Remove shadow on sign in button (#763).
  * Add cursor styles and active states (#675).
  * Move auth checks into decorator (#780).
  * Only resume if queue thread is running (#787).
  * Refactor queue resume/stop/start (#786).
  * Improve efficiency of source key management (#793).
  * Use ServerConnectionError from securedrop-sdk 0.0.13 (#784).
  * Only show last refresh if not logged in or network problems (#790).
  * Bug fix: Reset remaining attempts for each sync (#783).
  * Bug fix: Resolve potential crasher in queue (#744).
  * Bug fix: Ensure snippets update (#752).
  * Bug fix: Ensure that ReplyBox doesn't lose focus on sync (#740).
  * Bug fix: Ensure drafts are displayed when clicking between sources (#764).
  * Bug fix: Update slots and signals to match (#772).
  * Bug fix: Fix mkdir permission in AppArmor profile (#777).
  * Bug fix: Update source timestamp in UI (#778).
  * Bug fix: Fix CI due to virtualenv 20.0 installation (#794).

### 0.0.13

  * remove user refresh and replace with sync icon (#732)
  * build-requirements: update for production beta (#730)
  * No sync on ui operations (#721)
  * Use SecureQLabel for message previews (#720)
  * Show DD MMM format for source title (#719)
  * Add new metadata queue. (#715)
  * Improve performance of storage.get_remote_data (#709)
  * app/queue: prioritize user-triggered state changes (#708)
  * Fix HTML entities being escaped in speech bubbles. (#703)
  * Activity indicator for file download / decryption. (#702)
  * Rename VMs (#701)

### 0.0.12

  * Use revised VM names `sd-app` (was `sd-svs`), `sd-devices`
    (was `sd-export-usb`) and `sd-viewer` (was `sd-svs-disp`) throughout
    the application. Part of a workstation-wide VM rename operation described
    in https://github.com/freedomofpress/securedrop-workstation/issues/285
  * Delete sources using the general queue (#402)
  * Add a preview snippet for sources (#135)
  * Add a show/hide password feature on the login screen (#659)
  * Disable sync icon during active sync (#388)
  * Add keyboard shortcuts for sending replies (#606)
  * Add hover states for UI elements (#591)

### 0.0.11

  * Add apparmor profile (#673)
  * Add failure message for replies (#664)
  * Move metadata sync to api queue (#640)
  * Add print integration (#631)
  * Populate source list immediately upon login (#626)

### 0.0.10

  * Add Python 3.7/buster support (#568, #609)
  * Add export to USB support (#611, #547, #562, #563, #564)
  * Retry failed replies (#530)
  * Pause queue on auth errors, connection failures, and timeouts (#531)
  * Add pending reply status, persist replies in the database (#578)
  * Set realistic timeouts, scale file/message download timeouts using file size (#515, #567)
  * Update qrexec keyword prefix characters (#537)
  * Reply box no longer accepts rich text input (#580)
  * Format reply box placeholder text (#597)
  * Redesign FileWidget (#535)
  * Style conversation header (#543)
  * Login form submits if user presses Enter or Return (#615)
  * Enable changeable log levels (#603)
  * Remove borders around source list, send icon, and reply box (#505)
  * Move star and date in source widget (#506)
  * Polish source widget (#522)
  * Polish offline UI (#586)
  * Add branding image to left pane and polish styling (#520)
  * Add empty conversation view (#510)
  * Update fonts weights and colors (#502)
  * Bugfix: handle missing files during export and open (#566)
  * Bugfix: do not escape quotes in SecureQLabel (#516)
  * Bugfix: skip round trip to user endpoint during logic (#605, #621, #623)
  * Bugfix: fix bug of sources disappearing from source list (#620)
  * Bugfix: fix db warnings upon source deletion (#581)
  * Add more detailed developer documentation (#508)
  * Add documentation for updating dependencies (#536)
  * Ensure build/dev requirements files stay in sync (#602)
  * Parallelize test suite (#569)
  * Ignore third-party deprecation warnings (#576)
  * Add bandit to check target (#548)

### 0.0.9

  * Use Montserrat and Source Sans Pro (#493)
  * Same BG for scrollarea, conversation view, selected source (#494,#496)
  * Supports opening submissions in DispVMs from Qubes dev env (#490)
  * Center all popup windows (#487)
  * Use priority queue for job processing (#486)
  * Use SecureQLabel (#485)
  * Extract and display original document filenames (#452)
  * Save in-progress replies via persisting SourceConversationWrapper (#431)

### 0.0.8

  * Update SDK to 0.0.10, urllib to 1.24.3, and SQLAlchemy to 1.3.3 (#424)
  * Remove pipenv in favor of pip-tools (#372)

### 0.0.7

  * Update securedrop-sdk to 0.0.8 (#357)

### 0.0.6

  * Long lived threads are now de-authenticated on logout (#179)
  * updated requirements based on newly built wheels (#177)
  * Application no longer crashes when source collection is deleted on web
    interface (#176)
  * Improved input validation for login panel (#169)
  * Delete submissions on disk when deleted from server (#168)
  * Escape HTML in messages (#164)
  * Source list displayed by last_updated value (#158)
  * Show attachment icon when document count is greater than zero (#157)
  * Disable refresh when API call in progress (#154)
  * Fix crash in offline mode (#150)
  * Developer environment fixes (#148, #149, #152)

### 0.0.5-1

  * Package updated to apt-test-qubes did not include securedrop-sdk 0.4

### 0.0.5

  * Standardize dev env (#145)
  * Update securedrop-proxy to 0.0.4

### 0.0.4

  * Adds .desktop shortcut.

### 0.0.3

  * Fix and squash migrations (#129).
  * Don't hide two factor code while typing (#131).
  * Remove placeholder text from source list (#134).

### 0.0.2-1

  * Resolves venv paths in generated scripts (via dh-virtualenv)

### 0.0.2

  * Enable decryption and viewing of replies (#114).
  * Enable decryption and viewing of messages (#99).
  * Enable decryption and opening of files in a DispVM (#113).
  * Add status bar on bottom of application (#65).
  * Prevent concurrent application launches (#54).
  * Enable starring/unstarring of sources (#50).

### 0.0.1

  * Initial release.

## securedrop-export

### 0.3.0

 * Support Debian Bullseye
 * Improve error-handling
 * Update dependencies
 * Refactor path-traversal check for improved readability

### 0.2.6
  * Further validate target paths

### 0.2.5
  * Sets restrictive permissions, validates target paths

### 0.2.4
  * Removes mimetype associations and open-in-dvm desktop file

### 0.2.3

  * Adds gnome-disks to sd-devices
  * Documentation updates

### 0.2.2

  * Update mimetype handling

### 0.2.1

  * Open files in dvm by default

### 0.2.0

  * Initial beta release.

### 0.1.2

  * Adds logging (#17).

### 0.1.1

  * Initial release.

## securedrop-log

### 0.2.0

  * Supports logging in QubesOS 4.1.

### 0.1.2

  * Uses Qubes domain name instead of system hostname.

### 0.1.1

  * Infers hostname from system settings, if no config value found.

### 0.1.0

  * Initial beta release.

### 0.0.4

  * Converts into rsyslog based logging system.

### 0.0.3

  * Fixes typos MANIFEST.in and setup.py

### 0.0.2

  * Fixes execution permission for securedrop-log command.

### 0.0.1

  * Initial release.

## securedrop-proxy

### 0.4.1
  * Updated certifi to 2022.12.7 (#107)
  * Drop furl dependency (#105, #111)
  * Replace werkzeug dependency with basic string checks (#110, 115)

### 0.4.0

  * Reject JSON with duplicate keys (TOB-SDW-014) (#98)
  * Support Debian Bullseye (#100, #97)
  * Use reproducible wheels (#81, #85)
  * Dependency updates (#82, #88, #91, #93, #95, #96)

### 0.3.1

  * Moved proxy configuration to private volume (#79)
  * Added black and isort checks to standardise code formatting (#61)
  * Update urllib3 to version 1.25.10, requests to version 2.22.0, due to CVE-2020-26137 (#76).

### 0.3.0

  * Use incoming timeout value from JSON (#69).
  * Update PyYaml to 5.3.1 due to CVE-2020-1747 (#73).

### 0.2.1

  * Increase default timeout to 120s from 10s (#70)

### 0.2.0

  * Initial beta release.

### 0.1.7

  * Update Werkzeug to 0.16.0 due to CVE-2019-14806 (#64)

### 0.1.6

  * Fixes CI for git-lfs based package builds (#60)
  * Rename VMs (#59)
  * Restructures the code base with more object methods (#55)
  * Add quality control tools (#54)
  * Improve error handling, tests (#53)
  * Adds buster packaging in CI (#52)

### 0.1.5

  * Update build-requirements.txt to include wheels for Buster

### 0.1.4

  * Update urllib3 to version 1.24.3 or later due to CVE-2019-11324 (#35)
  * Remove pipenv in favor of pip-tools (#33)

### 0.1.3

  * Updated PyYAML to 5.1 and safe loading of YAML files
    #24 and #25

### 0.1.2

  * Update requirements: Remove dev requirements (#20), update wheel hashes
    (#21)

### 0.1.1-1

  * Resolves venv paths in generated scripts (via dh-virtualenv)

### 0.1.1

  * Update requests to 2.20.0

### 0.1.0

  * Initial release. (Closes: #XXX)

## securedrop-sdk

### 0.4.0

* Ensure support for common date string formats (#172)

### 0.3.2

* Update idna to 3.2 (#169)

### 0.3.1

* Update urllib3 to 1.26.6 to address CVE-2021-33503 (#166)
* Update certifi to 2021.5.30, idna to 2.8, requests to 2.26.0 (#167)

### 0.3.0

* Support "delete_conversation " endpoint (#158)

### 0.2.0

* Support "users" endpoint (#134).
* Update urllib3 from 1.25.8 to 1.25.10 (#136).
* Support "seen" endpoint (#140).
* Add "seen_by" as an attribute on the Submission and Reply objects (#140).

### 0.1.1

* Add journalist name to Reply object (#125).

### 0.1.0

* Pass timeout value to the proxy (#117).
* Update PyYAML to 5.3.1 (#120).

### 0.0.13

* Bug fix: return RequestTimeoutError and ServerConnectionError exceptions instead of AuthError, no longer raise KeyError when a file fails to download via the proxy (#109)
* Adds test cases and uses pip-tools for development dependency management (#112).

### 0.0.12

* Updates qrexec policy keyword character (#102).
* Expose journalist first and last name through the API (#105).

### 0.0.11

* Expose ETags in submission and reply downloads (#96).
* Update tests and test data for first and last name (#92).
* Bug fix: Ensure RequestTimeoutError is raised for submission and reply downloads (#95).

### 0.0.10

* Support logout endpoint (#88).

### 0.0.9

* Create a timeout exception to catch all possible timeouts from `requests` / Qubes RPC
* Remove mutable global state for the proxy VM name

### 0.0.8

* Revert return type of API.authenticate to bool

### 0.0.7

* Update PyYAML dependency to 5.1

### 0.0.6

* Fix auth header to user "Token" and not "token" (#56).
* Parse the new required field `filename` in the response when posting a reply (#54).

### 0.0.5

* Allow clients to set UUID of replies via API (#49).

### 0.0.4

* Rename default proxy VM from sd-journalist to sd-proxy (#43).
* Get stderr text when using Qubes proxy (#38).
* Parse reply UUID (#42).
* Fix incorrect error message when downloading a file (#36).

### 0.0.3

* Support UUID-only creation of Replies (#31).

### 0.0.2

* Support SDK use in a Qubes vault AppVM via securedrop-proxy (#21).
* Add journalist UUID as an attribute on the Reply object (#19).

### 0.0.1

* Initial alpha release.
