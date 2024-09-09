#include "utils.h"

int main(void)
{
	struct eager_output_test test = {
		.patterns =  {
			"apple",
			"banana",
			"carrot",
		},
		.inputs = {
			{ .input = "apple", .expected_ids = { 1 } },
			{ .input = "banana", .expected_ids = { 2 } },
			{ .input = "carrot", .expected_ids = { 3 } },
			{ .input = "apple banana", .expected_ids = { 1, 2 } },
			{ .input = "carrot fig apple", .expected_ids = { 1, 3 } },
		},
	};

	const bool min = getenv("MIN") != NULL;
	return run_test(&test, min, true);
}
