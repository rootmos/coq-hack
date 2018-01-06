open Printf

let find_n_valley f n =
  let rec go x (f0, x0) m =
    (*printf "x=%d f0=%d x0=%d m=%d\n" x f0 x0 m;*)
    match m with
    | _ when f0 = 0 -> x0 (* f is now constantly 0 *)
    | m when f0 = f x -> if (m+1) = n then x0 else go (x+1) (f0, x0) (m+1)
    | _ (* then f0 >= f x *) -> go (x+1) (f x, x) 0
  in go 1 (f 0, 0) 1

let f x = try [|7; 6; 6; 4; 3; 3; 3; 3; 2|].(x) with _ -> 0

let () =
  printf "1-valley=%d\n" (find_n_valley f 1);
  printf "2-valley=%d\n" (find_n_valley f 2);
  printf "3-valley=%d\n" (find_n_valley f 3);
  printf "4-valley=%d\n" (find_n_valley f 4)
