import type { Item } from "../../../../../types";

interface ItemProps {
  item: Item;
}

function Item({ item }: ItemProps) {
  // Placeholder for now
  return <div data-testid={`item-${item.uuid}`}>Item: {item.uuid}</div>;
}

export default Item;
