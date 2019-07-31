# Changelog

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
