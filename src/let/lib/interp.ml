(* 
  Name: Ricky Patel
  CWID: 20032062
  RPATEL29
  CS510A
*)

open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | IsEmpty(e) -> 
    eval_expr e >>= (function
      | TreeVal Empty -> return (BoolVal true)
      | TreeVal _ -> return (BoolVal false)
      | _ -> error "Expected a tree value")
  | EmptyTree(_t) -> 
    return (TreeVal Empty)
  | Node(e1,e2,e3) -> 
    eval_expr e1 >>= fun v1 ->
      eval_expr e2 >>= fun v2 ->
      eval_expr e3 >>= fun v3 ->
      (match (v2, v3) with
       | (TreeVal t2, TreeVal t3) -> return (TreeVal (Node (v1, t2, t3)))
       | _ -> error "TreeVal expected for both arguments")
  | CaseT(e1,e2,id1,id2,id3,e3) -> 
    eval_expr e1 >>= (function
    | TreeVal Empty -> eval_expr e2
    | TreeVal (Node (v, t1, t2)) -> 
      extend_env id1 v >>+
      extend_env id2 (TreeVal t1) >>+
      extend_env id3 (TreeVal t2) >>+
      eval_expr e3
    | _ -> error "Expected a TreeVal")
  | Record(fs) -> let rec eval_fields fields acc seen_names =
    match fields with
    | [] -> return (Record (List.rev acc))
    | (name, (_, expr)) :: rest ->
        if List.mem name seen_names then
          error "Record: duplicate fields"
        else
          eval_expr expr >>= fun value ->
          eval_fields rest ((name, (false, value)) :: acc) (name :: seen_names)
    in 
    eval_fields fs [] []
  | Proj(e,id) -> eval_expr e >>= (function
    | Record fields ->
      let rec find_field id = function
        | [] -> error "Proj: field does not exist"
        | (name, (_, value)) :: _ when name = id -> return value
        | _ :: rest -> find_field id rest 
      in
      find_field id fields
    | _ -> error "Expected a record")
  and
  eval_exprs : expr list -> (exp_val list) ea_result =
    fun es ->
      match es with
      | [] -> return []
      | h::t -> eval_expr h >>= fun i ->
        eval_exprs t >>= fun l -> return (i::l)
  | _ -> failwith "Not implemented yet!"

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


