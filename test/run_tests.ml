let test_suites : unit Alcotest.test list = [ "oracle", Test_oracle.test_cases ]
let () = Alcotest.run "mini_hh" test_suites