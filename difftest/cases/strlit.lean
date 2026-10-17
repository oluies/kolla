/-- String literals and their reduction to a list of characters. -/
theorem lenLit : "abc".length = 3 := rfl
theorem appendLit : "ab" ++ "cd" = "abcd" := rfl
theorem dataLit : "ab".data = ['a', 'b'] := rfl
theorem eqLit : ("abc" == "abc") = true := rfl
