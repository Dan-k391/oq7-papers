import CompactMaxwell.SixVectorEquality
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (A 0 1).transpose = D * A 0 1 * D := reciprocal 0 1
