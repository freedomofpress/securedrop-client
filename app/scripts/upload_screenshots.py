#!/usr/bin/env python3
"""
Upload screenshots to Weblate and associate them with source strings keyed by
i18next translation key.

Usage:
    WEBLATE=https://weblate.example.org \
        WEBLATE_API_TOKEN=your_token \
        python scripts/upload_screenshots.py \
            --project myproject \
            --component mycomponent \
            screenshots/

Environment variables:
    WEBLATE               - Base URL of the Weblate instance (required)
    WEBLATE_API_TOKEN     - API authentication token (required)
    WEBLATE_EXTRA_COOKIES - JSON object with extra cookies to include in requests (optional)
                            Example: '{"VouchCookie": "foo"}'
"""

import argparse
import json
import logging
import os
from pathlib import Path

import requests

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
)
logger = logging.getLogger(__name__)

# Timeout for API requests (connect timeout, read timeout) in seconds
REQUEST_TIMEOUT = (10, 30)


class WeblateClient:
    def __init__(self, base_url: str, api_token: str, extra_cookies: dict | None = None):
        self.base_url = base_url.rstrip("/")
        self.session = requests.Session()
        self.session.headers.update(
            {
                "Authorization": f"Token {api_token}",
                "Accept": "application/json",
            }
        )
        if extra_cookies:
            self.session.cookies.update(extra_cookies)

    def _paginate(self, url: str, params: dict | None = None) -> list:
        """Fetch all pages from a paginated API endpoint."""
        results = []
        params = params or {}

        while url:
            response = self.session.get(url, params=params, timeout=REQUEST_TIMEOUT)
            response.raise_for_status()
            data = response.json()

            results.extend(data.get("results", []))
            url = data.get("next")
            params = {}  # params only needed for first request

        return results

    def get_units(self, project: str, component: str, language: str) -> list:
        """Fetch all translation units for a component/language."""
        url = f"{self.base_url}/api/units/"
        query = f"project:{project} component:{component} language:{language}"
        return self._paginate(url, params={"q": query})

    def get_screenshots(self) -> list:
        """Fetch all screenshots."""
        url = f"{self.base_url}/api/screenshots/"
        return self._paginate(url)

    def upload_screenshot(
        self, name: str, filepath: Path, project_slug: str, component_slug: str, language_code: str
    ) -> int:
        """Upload a new screenshot and return its ID."""
        url = f"{self.base_url}/api/screenshots/"
        data = {
            "name": name,
            "project_slug": project_slug,
            "component_slug": component_slug,
            "language_code": language_code,
        }
        logger.debug(f"POST {url} data={data} files={{image: {filepath.name}}}")
        with open(filepath, "rb") as f:
            response = self.session.post(
                url,
                data=data,
                files={"image": (filepath.name, f, "image/png")},
                timeout=REQUEST_TIMEOUT,
            )
        if not response.ok:
            logger.debug(f"Response {response.status_code}: {response.text}")
        response.raise_for_status()
        # Parse screenshot ID from file_url: .../api/screenshots/(id)/file/
        file_url = response.json()["file_url"]
        screenshot_id = int(file_url.rstrip("/").split("/")[-2])
        logger.info(f"Uploaded new screenshot: {name} (ID: {screenshot_id})")
        return screenshot_id

    def replace_screenshot(self, screenshot_id: int, filepath: Path) -> None:
        """Replace an existing screenshot's image."""
        url = f"{self.base_url}/api/screenshots/{screenshot_id}/file/"
        logger.debug(f"POST {url} files={{image: {filepath.name}}}")
        with open(filepath, "rb") as f:
            response = self.session.post(
                url,
                files={"image": (filepath.name, f, "image/png")},
                timeout=REQUEST_TIMEOUT,
            )
        if not response.ok:
            logger.debug(f"Response {response.status_code}: {response.text}")
        response.raise_for_status()
        logger.info(f"Replaced screenshot ID {screenshot_id} with {filepath}")

    def get_screenshot_units(self, screenshot_id: int) -> set[int]:
        """Get the set of unit IDs currently associated with a screenshot."""
        url = f"{self.base_url}/api/screenshots/{screenshot_id}/"
        response = self.session.get(url, timeout=REQUEST_TIMEOUT)
        response.raise_for_status()
        return set(response.json().get("units", []))

    def associate_unit(self, screenshot_id: int, unit_id: int) -> None:
        """Associate a unit with a screenshot (idempotent)."""
        url = f"{self.base_url}/api/screenshots/{screenshot_id}/units/"
        data = {"unit_id": unit_id}
        logger.debug(f"POST {url} data={data}")
        response = self.session.post(url, data=data, timeout=REQUEST_TIMEOUT)
        if not response.ok:
            logger.debug(f"Response {response.status_code}: {response.text}")
        response.raise_for_status()
        logger.info(f"Associated unit {unit_id} with screenshot {screenshot_id}")


def load_screenshot_files(screenshots_dir: Path) -> dict[str, Path]:
    """
    Load screenshot files and map i18next keys to file paths.
    E.g., "SignIn.title.png" -> key "SignIn.title"
    """
    screenshot_files = {}
    for path in screenshots_dir.glob("*.png"):
        # Remove .png extension to get the i18next key
        key = path.stem
        screenshot_files[key] = path

    logger.info(f"Found {len(screenshot_files)} screenshot files in {screenshots_dir}")
    return screenshot_files


def main():
    parser = argparse.ArgumentParser(
        description="Upload screenshots to Weblate and associate with translation units"
    )
    parser.add_argument(
        "--project",
        required=True,
        help="Weblate project slug",
    )
    parser.add_argument(
        "--component",
        required=True,
        help="Weblate component slug",
    )
    parser.add_argument(
        "--language",
        default="en",
        help="Source language code (default: en)",
    )
    parser.add_argument(
        "screenshots_dir",
        type=Path,
        help="Directory containing screenshot PNG files",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be done without making changes",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Enable verbose logging",
    )
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    weblate_url = os.environ.get("WEBLATE")
    if not weblate_url:
        raise ValueError("WEBLATE environment variable is required")

    api_token = os.environ.get("WEBLATE_API_TOKEN")
    if not api_token:
        raise ValueError("WEBLATE_API_TOKEN environment variable is required")

    extra_cookies = None
    extra_cookies_json = os.environ.get("WEBLATE_EXTRA_COOKIES")
    if extra_cookies_json:
        try:
            extra_cookies = json.loads(extra_cookies_json)
        except json.JSONDecodeError as e:
            raise ValueError(f"WEBLATE_EXTRA_COOKIES is not valid JSON: {e}") from e
        if not isinstance(extra_cookies, dict):
            raise TypeError(
                "WEBLATE_EXTRA_COOKIES must be a JSON object mapping cookie names to values, "
                f"got {type(extra_cookies).__name__}"
            )

    if not args.screenshots_dir.is_dir():
        raise FileNotFoundError(f"Screenshots directory not found: {args.screenshots_dir}")

    client = WeblateClient(weblate_url, api_token, extra_cookies)
    screenshot_files = load_screenshot_files(args.screenshots_dir)

    if not screenshot_files:
        raise FileNotFoundError(f"No screenshot files found in {args.screenshots_dir}")

    # Map: i18next key -> (set of unit IDs, screenshot ID or None)
    screenshots_to_units: dict[str, tuple[set[int], int | None]] = {}

    # Fetch units and match to screenshot files
    logger.info("Fetching translation units...")
    units = client.get_units(args.project, args.component, args.language)
    logger.info(f"Found {len(units)} translation units")

    for unit in units:
        key = unit["context"]
        if key in screenshot_files:
            prev = screenshots_to_units.get(key, (set(), None))
            screenshots_to_units[key] = (prev[0] | {unit["id"]}, prev[1])
            logger.debug(f"Matched unit {unit['id']} to screenshot key: {key}")

    # Fetch existing screenshots and match to our files
    logger.info("Fetching existing screenshots...")
    screenshots = client.get_screenshots()
    logger.info(f"Found {len(screenshots)} existing screenshots")

    translation_url = f"/api/translations/{args.project}/{args.component}/{args.language}/"

    for screenshot in screenshots:
        # Filter to our component
        if not screenshot["translation"].endswith(translation_url):
            continue

        name = screenshot["name"]
        if name not in screenshot_files:
            continue

        prev = screenshots_to_units.get(name, (set(), None))
        if prev[1] is not None and prev[1] != screenshot["id"]:
            logger.error(f"Skipping duplicate screenshot for key: {name}")
            continue

        screenshots_to_units[name] = (prev[0], prev[1] or screenshot["id"])
        logger.debug(f"Found existing screenshot {screenshot['id']} for key: {name}")

    # Process each screenshot
    logger.info(f"Processing {len(screenshots_to_units)} screenshots...")

    for key, (unit_ids, screenshot_id) in screenshots_to_units.items():
        filepath = screenshot_files[key]

        if args.dry_run:
            action = "replace" if screenshot_id else "upload"
            logger.info(f"[DRY RUN] Would {action} screenshot: {key}")
            logger.info(f"[DRY RUN] Would associate with {len(unit_ids)} units: {unit_ids}")
            continue

        # Upload or replace screenshot
        if screenshot_id is None:
            screenshot_id = client.upload_screenshot(
                key, filepath, args.project, args.component, args.language
            )
        else:
            client.replace_screenshot(screenshot_id, filepath)

        # Associate with units (idempotent - rely on associate_unit handling duplicates)
        for unit_id in unit_ids:
            client.associate_unit(screenshot_id, unit_id)

    # Report screenshots without matching units (including those that exist in
    # Weblate but have zero matching units)
    unmatched = [
        key
        for key in screenshot_files
        if key not in screenshots_to_units or not screenshots_to_units[key][0]
    ]
    if unmatched:
        logger.warning(
            f"{len(unmatched)} screenshots have no matching translation units: {unmatched}"
        )

    logger.info("Done!")


if __name__ == "__main__":
    main()
