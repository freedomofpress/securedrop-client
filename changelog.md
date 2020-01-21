# Changelog

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
