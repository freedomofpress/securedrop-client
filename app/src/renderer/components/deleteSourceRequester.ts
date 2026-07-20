let openDeleteModal: ((sources: Set<string>) => void) | null = null;

export function requestDeleteSource(sources: Set<string>) {
  openDeleteModal?.(sources);
}

export function setDeleteSourceHandler(
  handler: ((sources: Set<string>) => void) | null,
) {
  openDeleteModal = handler;
}
