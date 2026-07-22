from securedrop_client.gui.shortcuts import Shortcuts


def test_all_values_are_unique():
    # Get all the values in the enum
    enum_values = []
    for value in Shortcuts.__members__.values():
        enum_values.append(value.value)

    # Check that all values are unique
    assert len(enum_values) == len(set(enum_values)), "Enum values are not unique"
