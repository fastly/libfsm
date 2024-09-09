#include "utils.h"

#define ALL 0

int main(void)
{
	/* assert(!"fixme: revisit once access patterns are more efficient"); */

	struct eager_output_test test = {
		.patterns =  {
			"apple",
			"banana",
			"carrot",
#if ALL
			"durian",
			"eggplant",
			"fig",
			"grapefruit",
			"hazelnut",
			"iceberg lettuce",
			"jicama",
#endif
		},
		.inputs = {
			{ .input = "apple", .expected_ids = { 1 } },
			{ .input = "banana", .expected_ids = { 2 } },
			{ .input = "carrot", .expected_ids = { 3 } },
#if ALL
			{ .input = "durian", .expected_ids = { 4 } },
			{ .input = "eggplant", .expected_ids = { 5 } },
			{ .input = "fig", .expected_ids = { 6 } },
			{ .input = "grapefruit", .expected_ids = { 7 } },
			{ .input = "hazelnut", .expected_ids = { 8 } },
			{ .input = "iceberg lettuce", .expected_ids = { 9 } },
			{ .input = "jicama", .expected_ids = { 10 } },
#endif
			{ .input = "apple banana carrot", .expected_ids = { 1, 2, 3 } },
		},
	};

	const bool min = getenv("MIN") != NULL;
	/* return run_test(&test, false, true); */
	return run_test(&test, min, true);
}
