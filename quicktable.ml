(* MIT License
 *
 * Copyright (c) 2022 Samuel B. Cohen
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *)

(* quicktable.ml
 *
 * Given a set of boolean equations, this program
 * will generate the truth table corresponding
 * to the given set of equations and print it
 * to stdout.
 *)

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
type env = bool StringMap.t

type term = In of string
          | And of term * term
          | Or of term * term
          | Xor of term * term
          | Not of term
type eq = string * term

let free_vars_in_term (t : term) =
  let rec f (t : term) (set : StringSet.t) =
    match t with
    | In nm -> StringSet.add nm set
    | And (a, b) | Or (a, b) | Xor (a, b) ->
       StringSet.union (f a set) (f b StringSet.empty)
    | Not a -> f a set in
  f t StringSet.empty
;;

let eval (t : term) (vars : env) =
  let rec ev (t : term) =
    match t with
    | In nm -> StringMap.find nm vars
    | And (a, b) -> ev a && ev b
    | Or  (a, b) -> ev a || ev b
    | Xor (a, b) -> (ev a && not (ev b)) || (not (ev a) && ev b)
    | Not a -> not (ev a) in
  ev t
;;

let rec pow2 (n : int) =
  if n = 0 then 1
  else 2 * pow2 (n - 1)
;;

let int_to_binary (n_digits : int) (n : int) =
  let rec f (n : int) (digits : int) =
    if digits = n_digits then []
    else if n > 0
    then (Int.rem n 2 = 1)::(f (n / 2) (digits + 1))
    else if digits < n_digits
    then List.init (n_digits - digits) (fun _ -> false)
    else []
  in
  List.rev (f n 0)
;;

exception Uneven_Bindings
(* raise Uneven_Bindings if the number of vars is not equal to 
 * the number of values *)
let rec create_bindings (vars : string Seq.t) (values : bool Seq.t) =
  match vars (), values () with
  | Seq.Nil, Seq.Nil -> fun () -> Seq.Nil
  | Seq.Cons (var, rest_vars), Seq.Cons (value, rest_values) ->
     fun () ->
     Seq.Cons ((var, value), create_bindings rest_vars rest_values)
  | _ -> raise Uneven_Bindings
;;

let enumerate_eqs (eqs : eq list) =
  let free_vars = List.fold_left (fun fvs (_, term) ->
                      StringSet.union fvs (free_vars_in_term term))
                    StringSet.empty eqs in
  let free_vars_seq = StringSet.to_seq free_vars in
  let n_free_vars = StringSet.cardinal free_vars in
  let n_perms = pow2 n_free_vars in
  let row_inputs = List.init n_perms (int_to_binary n_free_vars) in
  let row_outputs = List.map (fun row_input ->
                        let row_input_seq = List.to_seq row_input in
                        let bindings = create_bindings free_vars_seq row_input_seq in
                        let env = StringMap.of_seq bindings in
                        List.map (fun (name, term) ->
                            eval term env) eqs) row_inputs in
  row_inputs, row_outputs
;;

let bool_to_string = function
  | true  -> "1"
  | false -> "0"
;;

let pad_string (s : string) (length : int) =
  let s_length = String.length s in
  if s_length > length then
    String.sub s 0 length
  else
    let n_spaces = length - s_length in
    s ^ String.init n_spaces (fun _ -> ' ')
;;

let print_table (eqs : eq list) (inputs : bool list list) (outputs : bool list list) =
  let free_vars = List.fold_left (fun fvs (_, term) ->
                      StringSet.union fvs (free_vars_in_term term))
                    StringSet.empty eqs in
  let free_vars_seq = StringSet.to_seq free_vars in
  let input_labels = List.of_seq free_vars_seq in
  let output_labels = List.map fst eqs in
  let input_column_widths = List.map String.length input_labels in
  let output_column_widths = List.map String.length output_labels in
  (* print labels *)
  let label_string = String.concat " " input_labels
                     ^ " | "
                     ^ String.concat " " output_labels in
  print_endline label_string;
  (* print hline *)
  let hline_string = String.init (String.length label_string) (fun _ -> '=') in
  print_endline hline_string;
  (* print rows *)
  List.iter2 (fun input_row output_row ->
      let print_row (row : bool list) (widths : int list) =
        let strs =
          List.fold_right2 (fun value width strings ->
              (pad_string (bool_to_string value) width)::strings)
            row widths [] in
        print_string (String.concat " " strs) in
      
      print_row input_row input_column_widths;
      print_string " | ";
      print_row output_row output_column_widths;
      print_newline ())
    inputs outputs
;;

let analyze (spec : eq list) =
  let inputs, outputs = enumerate_eqs spec in
  print_table spec inputs outputs
;;

[@@@ocaml.warning "-26"]
let spec =
  let i (s : string) = In s        in (* input *)
  let (&&)  a b = And (a, b)       in (* and   *)
  let (||)  a b = Or  (a, b)       in (* or    *)
  let (^^)  a b = Xor (a, b)       in (* xor   *)
  let (!)   a   = Not a            in (* not   *)
  let (&&!) a b = Not (And (a, b)) in (* nand  *)
  let (||!) a b = Not (Or  (a, b)) in (* nor   *)
  let (^^!) a b = Not (Xor (a, b)) in (* xnor  *)
  [
    "sum"  , (i "a" ^^ i "b") ^^ i "c";
    "carry", (i "a" && i "b") ^^ (i "c" && (i "a" ^^ i "b"))
  ]
;;

analyze spec
;;
