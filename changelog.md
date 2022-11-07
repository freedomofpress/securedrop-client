# Changelog

## 0.8.1
* Add experimental support for a custom timeout that allows the SecureDrop Client to retrieve a larger number of sources (#1552)

## 0.8.0
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

## 0.7.0
* Clear global mouse selection after login (#1477)
* Update securedrop-sdk from version 0.3.2 to 0.4.0 (#1466)
* Add journalist read receipts (#1417, #1449, #1471)
* Speed up deletion of local files and database records (#1432, #1458, #1468, #1473)
* Add feature to download all files from a single source (#1388, #1448)
* Always invalidate the user when logging out (#1454)
* Refactors around user actions (#1447, #1400)
* Developer dependency updates for Pillow and pip-tools (#1433)

## 0.6.0
* Speed up source deletion (#1386, #1415)
* Use /users endpoint for managing journalist accounts (#1397)
* UI fix to bottom margin in conversation view (#1391)
* (Dev) Refactors that break up the widgets module into smaller components (#1377-1383, #1390, #1393, #1394)
* (Dev) Use Debian Stable container images in CI (#1385)
* (Dev) New templates for creating different types of GitHub Issues (#1392)
* (Dev) Add localization testing task to the release GitHub Issue template (#1401)

## 0.5.1
* Fix Python symlink, which broke package in 0.5.0

## 0.5.0

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

## 0.4.1

* Prevent path traversal in downloaded files (#1226)
* Scale source list, preview and conversation view on resize (#1211, #1206)
* (Dev) Add semgrep for static analysis, including an initial ruleset (#1226)
* (Dev) Remove obsolete MIME setup in run.sh (#1215)
* (Dev) Switch to using reproducibly built wheels (#1203)
* (Dev) Update development dependencies (#1208, #1222)
* (Docs) Incorporate Code of Conduct updates (#1216) 

## 0.4.0

* Support read/unread and track who sees a file, message, or reply (#1165)
* No longer expire source test key (#1180)
* Restyle source widgets and source selection indicators (#1191)
* No longer maximize client window if it's already open on login (#1192)
* Update securedrop-sdk version to 0.2.0 (#1172)
* (Dev) update macOS development requirements (#1183)

## 0.3.0

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

## 0.2.1

* Reformat the code with black and isort (#1115)
* Support multi-source deletions in one sync (#1114)
* Support more screen resolutions (#1103)
* Move CSS strings to CSS files and add new CSS tests (#1082)
* Prevent addition of duplicated API jobs (#975)

## 0.2.0

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

## 0.1.6

* Fix truncation and alignment issues in conversation view (#1029).

## 0.1.5

* Update source list ordering when conversation is updated (#1013).
* Do not show tooltips on short strings (#1016).

## 0.1.4

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

## 0.1.3

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

## 0.1.2

 * Update branding bar artwork (#871).
 * Remove "downloading file" message in sync area (#881).
 * Bug fix: Only force login when we're not already logged out (#884).
 * Bug fix: Retry source deletion jobs (#879).
 * Bug fix: Enter no longer closes print and export dialogs (#855).
 * Bug fix: Ensure that ReplyBox is updated after client gets source key (#864).
 * Bug fix: Ensure that we delete source collection when source is deleted (#866).
 * Bug fix: Ensure that we delete Python wrappers for deleted items (#887, #890, #898).

## 0.1.1

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

## 0.1.0

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

## 0.0.13

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

## 0.0.12

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

## 0.0.11

  * Add apparmor profile (#673)
  * Add failure message for replies (#664)
  * Move metadata sync to api queue (#640)
  * Add print integration (#631)
  * Populate source list immediately upon login (#626)

## 0.0.10

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

## 0.0.9

  * Use Montserrat and Source Sans Pro (#493)
  * Same BG for scrollarea, conversation view, selected source (#494,#496)
  * Supports opening submissions in DispVMs from Qubes dev env (#490)
  * Center all popup windows (#487)
  * Use priority queue for job processing (#486)
  * Use SecureQLabel (#485)
  * Extract and display original document filenames (#452)
  * Save in-progress replies via persisting SourceConversationWrapper (#431)

## 0.0.8

  * Update SDK to 0.0.10, urllib to 1.24.3, and SQLAlchemy to 1.3.3 (#424)
  * Remove pipenv in favor of pip-tools (#372)

## 0.0.7

  * Update securedrop-sdk to 0.0.8 (#357)

## 0.0.6

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

## 0.0.5-1

  * Package updated to apt-test-qubes did not include securedrop-sdk 0.4

## 0.0.5

  * Standardize dev env (#145)
  * Update securedrop-proxy to 0.0.4

## 0.0.4

  * Adds .desktop shortcut.

## 0.0.3

  * Fix and squash migrations (#129).
  * Don't hide two factor code while typing (#131).
  * Remove placeholder text from source list (#134).

## 0.0.2-1

  * Resolves venv paths in generated scripts (via dh-virtualenv)

## 0.0.2

  * Enable decryption and viewing of replies (#114).
  * Enable decryption and viewing of messages (#99).
  * Enable decryption and opening of files in a DispVM (#113).
  * Add status bar on bottom of application (#65).
  * Prevent concurrent application launches (#54).
  * Enable starring/unstarring of sources (#50).

## 0.0.1

  * Initial release.
