#include "utils.h"

int main(void)
{
	struct eager_endid_test test = {
		.patterns =  { "abcde$" },
		.inputs = {
			{ .input = "abcde", .expected_ids = { 1 } },
			{ .input = "Xabcde", .expected_ids = { 1 } },
		},
	};
	return run_test(&test, false, true);
}
