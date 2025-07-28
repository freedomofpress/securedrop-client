import type { SourceWithItems } from "../../../../types";

interface ItemsProps {
  sourceWithItems: SourceWithItems | null;
}

function Items({ sourceWithItems }: ItemsProps) {
  if (!sourceWithItems) return null;

  return <p>TODO: implement items for {sourceWithItems.items.length} items</p>;
}

export default Items;
