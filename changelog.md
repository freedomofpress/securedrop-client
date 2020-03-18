# Changelog

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
  * Update obselete original_filename usage in file_ready (#773).
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
