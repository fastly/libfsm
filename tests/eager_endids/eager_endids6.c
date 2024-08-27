#include "utils.h"

int main(void)
{
	assert(!"fixme: revisit once remap_eager_endids is more efficient");

	struct eager_endid_test test = {
		.patterns =  {
			"apple",
			"banana",
			"carrot",
			"durian",
			"eggplant",
			"fig",
			"grapefruit",
			"hazelnut",
			"iceberg lettuce",
			"jicama",
		},
		.inputs = {
			{ .input = "apple", .expected_ids = { 1 } },
			{ .input = "banana", .expected_ids = { 2 } },
			{ .input = "carrot", .expected_ids = { 3 } },
			{ .input = "durian", .expected_ids = {4} },
			{ .input = "eggplant", .expected_ids = {5} },
			{ .input = "fig", .expected_ids = {6} },
			{ .input = "grapefruit", .expected_ids = {7} },
			{ .input = "hazelnut", .expected_ids = {8} },
			{ .input = "iceberg lettuce", .expected_ids = {9} },
			{ .input = "jicama", .expected_ids = {10} },
			{ .input = "apple banana fig", .expected_ids = {1, 2, 6} },
		},
	};
	return run_test(&test, false, true);
}
