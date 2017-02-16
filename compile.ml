open Printf
open Types
open Pretty

type 'a envt = (string * 'a) list

let const_true_value = 0xFFFFFFFF
let const_true = Sized(DWORD_PTR, HexConst(const_true_value))
let const_false_value = 0x7FFFFFFF
let const_false = Sized(DWORD_PTR, HexConst(const_false_value))
let bool_mask = Sized(DWORD_PTR, HexConst(0x80000000))
let tag_as_bool = Sized(DWORD_PTR, HexConst(0x00000001))

let err_COMP_NOT_NUM   = Sized(DWORD_PTR, HexConst(1))
let err_ARITH_NOT_NUM  = Sized(DWORD_PTR, HexConst(2))
let err_LOGIC_NOT_BOOL = Sized(DWORD_PTR, HexConst(3))
let err_IF_NOT_BOOL    = Sized(DWORD_PTR, HexConst(4))
let err_OVERFLOW       = Sized(DWORD_PTR, HexConst(5))

(* You may find some of these helpers useful *)
let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
    | [] -> None
    | (DFun(fname, _, _, _) as d)::ds_rest ->
      if name = fname then Some(d) else find_decl ds_rest name

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
    | [] -> false
    | x::xs -> (elt = x) || (find_one xs elt)

let rec find_dup (l : 'a list) : 'a option =
  match l with
    | [] -> None
    | [x] -> None
    | x::xs -> if find_one xs x then Some(x) else find_dup xs

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;

let well_formed (p : (Lexing.position * Lexing.position) program) : exn list =
    let rec wf_E e decl_list env (* other parameters may be needed here *) =
        match e with
        | ELet(bind_list, body, pos) ->
            let shadow_check var =
                let rec find_shadow ls name =
                    match ls with
                    | [] -> None
                    | (id, pos)::rest ->
                        if id = name then Some(pos) else find_shadow rest name in
                let (name, pos) = var in
                match find_shadow env name with
                | None -> []
                | Some(dup_pos) -> [ShadowId(name, pos, dup_pos)] in
            let vars_list  = List.map (fun b -> let (n, _, p) = b in (n, p)) bind_list in
            let vars_excns = dup_excns vars_list in
            let shadow_excns = List.flatten(List.map shadow_check vars_list) in
            let expr_list  = List.map (fun b -> let (_, e, _) = b in e) bind_list in
            let expr_excns = List.flatten(List.map (fun e -> wf_E e decl_list env) expr_list) in
            let body_excns = wf_E body decl_list (vars_list@env) in
            vars_excns @ shadow_excns @ expr_excns @ body_excns
        | EPrim1(_, expr, pos) ->
            wf_E expr decl_list env
        | EPrim2(_, expr1, expr2, pos) ->
            wf_E expr1 decl_list env @
            wf_E expr2 decl_list env
        | EIf(cond, thn, els, pos) ->
            wf_E cond decl_list env @
            wf_E thn decl_list env @
            wf_E els decl_list env
        | ENumber(x, pos) ->
            if x > 1073741823 || x < -1073741824 then
                [Overflow(x, pos)]
            else
                []
        | EBool(_, _) ->
            []
        | EId(id, pos) ->
            if find_one (List.map fst env) id then
                []
            else
                [UnboundId(id, pos)]
        | EApp(func, expr_list, pos) ->
            match (find_decl decl_list func) with
            | None ->
                [UnboundFun(func, pos)]
            | Some(func) ->
                let DFun(_, vars_list, _, _) = func in
                let decl_numargs = List.length vars_list in
                let expr_numargs = List.length expr_list in
                if decl_numargs != expr_numargs then
                    [Arity(decl_numargs, expr_numargs, pos)]
                else
                    List.flatten(List.map (fun e -> wf_E e decl_list env) expr_list)
    and wf_D d decl_list =
        let DFun(name, env, body, pos) = d in
        let vars_excns = dup_excns env in
        let body_excns = wf_E body decl_list env in
        vars_excns @ body_excns
    and check_funcs decl_list =
        match decl_list with
        | [] -> []
        | DFun(name, _, _, pos)::rest ->
            match find_decl rest name with
            | None -> check_funcs rest
            | Some(DFun(_, _, _, dup_pos)) ->
                [DuplicateFun(name, pos, dup_pos)] @ check_funcs rest
    and dup_excns env =
        let rec find_dup_pos ls name =
          match ls with
            | [] -> None
            | (id, pos)::rs -> if var = id then Some(pos) else find_dup_pos rs name in
        match env with
        | [] -> []
        | x::xs -> (match find_dup_pos xs (fst x) with
            | None -> dup_excns xs
            | Some(dup_pos) -> DuplicateId(fst x, dup_pos, snd x)::dup_excns xs
        )
    in match p with
    | Program(decls, body, _) ->
        List.flatten(List.map (fun f -> wf_D f decls) decls) @
        check_funcs decls @
        wf_E body decls []
;

type tag = int
let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next in
  let rec helpE (e : 'a expr) : tag expr =
    match e with
    | EId(x, _) -> EId(x, tag())
    | ENumber(n, _) -> ENumber(n, tag())
    | EBool(b, _) -> EBool(b, tag())
    | EPrim1(op, e, _) ->
       let prim_tag = tag() in
       EPrim1(op, helpE e, prim_tag)
    | EPrim2(op, e1, e2, _) ->
       let prim_tag = tag() in
       EPrim2(op, helpE e1, helpE e2, prim_tag)
    | ELet(binds, body, _) ->
       let let_tag = tag() in
       ELet(List.map (fun (x, b, _) -> let t = tag() in (x, helpE b, t)) binds, helpE body, let_tag)
    | EIf(cond, thn, els, _) ->
       let if_tag = tag() in
       EIf(helpE cond, helpE thn, helpE els, if_tag)
    | EApp(name, args, _) ->
       let app_tag = tag() in
       EApp(name, List.map helpE args, app_tag)
  and helpD d =
    match d with
    | DFun(name, args, body, _) ->
       let fun_tag = tag() in
       DFun(name, List.map (fun (a, _) -> (a, tag())) args, helpE body, fun_tag)
  and helpP p =
    match p with
    | Program(decls, body, _) ->
       Program(List.map helpD decls, helpE body, 0)
  in helpP p

let rec untag (p : 'a program) : unit program =
  let rec helpE e =
    match e with
    | EId(x, _) -> EId(x, ())
    | ENumber(n, _) -> ENumber(n, ())
    | EBool(b, _) -> EBool(b, ())
    | EPrim1(op, e, _) ->
       EPrim1(op, helpE e, ())
    | EPrim2(op, e1, e2, _) ->
       EPrim2(op, helpE e1, helpE e2, ())
    | ELet(binds, body, _) ->
       ELet(List.map(fun (x, b, _) -> (x, helpE b, ())) binds, helpE body, ())
    | EIf(cond, thn, els, _) ->
       EIf(helpE cond, helpE thn, helpE els, ())
    | EApp(name, args, _) ->
       EApp(name, List.map helpE args, ())
  and helpD d =
    match d with
    | DFun(name, args, body, _) ->
       DFun(name, List.map (fun (a, _) -> (a, ())) args, helpE body, ())
  and helpP p =
    match p with
    | Program(decls, body, _) ->
       Program(List.map helpD decls, helpE body, ())
  in helpP p

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ALet(x, c, b, _) ->
       let let_tag = tag() in
       ALet(x, helpC c, helpA b, let_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1(op, e, _) ->
       let prim_tag = tag() in
       CPrim1(op, helpI e, prim_tag)
    | CPrim2(op, e1, e2, _) ->
       let prim_tag = tag() in
       CPrim2(op, helpI e1, helpI e2, prim_tag)
    | CIf(cond, thn, els, _) ->
       let if_tag = tag() in
       CIf(helpI cond, helpA thn, helpA els, if_tag)
    | CApp(name, args, _) ->
       let app_tag = tag() in
       CApp(name, List.map helpI args, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmId(x, _) -> ImmId(x, tag())
    | ImmNum(n, _) -> ImmNum(n, tag())
    | ImmBool(b, _) -> ImmBool(b, tag())
  and helpD d =
    match d with
    | ADFun(name, args, body, _) ->
       let fun_tag = tag() in
       ADFun(name, args, helpA body, fun_tag)
  and helpP p =
    match p with
    | AProgram(decls, body, _) ->
       AProgram(List.map helpD decls, helpA body, 0)
  in helpP p


let anf (p : tag program) : unit aprogram =
    let rec helpP (p : tag program) : unit aprogram =
      match p with
      | Program(decls, body, _) -> AProgram(List.map helpD decls, helpA body, ())
    and helpD (d : tag decl) : unit adecl =
      match d with
      | DFun(name, args, body, _) -> ADFun(name, List.map fst args, helpA body, ())
    and helpA e : unit aexpr =
      let (ans, ans_setup) = helpC e in
      List.fold_right
          (fun (bind, exp) body -> ALet(bind, exp, body, ()))
          ans_setup
          (ACExpr ans)
    and helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) =
      match e with
      | EPrim1(op, arg, _) ->
         let (arg_imm, arg_setup) = helpI arg in
         (CPrim1(op, arg_imm, ()), arg_setup)
      | EPrim2(op, left, right, _) ->
         let (left_imm, left_setup) = helpI left in
         let (right_imm, right_setup) = helpI right in
         (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
      | EIf(cond, _then, _else, _) ->
         let (cond_imm, cond_setup) = helpI cond in
         (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
      | ELet([], body, _) -> helpC body
      | ELet((bind, exp, _)::rest, body, pos) ->
         let (exp_ans, exp_setup) = helpC exp in
         let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
         (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
      | EApp(funname, args, _) ->
         let (args_list, setup_list) =
             List.fold_left
             (fun (prev_ans, prev_setup) expr ->
                 let (ans, setup) = helpI expr in
                 (ans::prev_ans, setup@prev_setup)
             )
             ([], [])
             args in
         (CApp(funname, args_list, ()), setup_list)
      | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)
    and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
      match e with
      | ENumber(n, _) ->
          (ImmNum(n, ()), [])
      | EBool(b, _) ->
          (ImmBool(b, ()), [])
      | EId(name, _) ->
          (ImmId(name, ()), [])
      | EPrim1(op, arg, tag) ->
         let name = sprintf "unary_%d" tag in
         let (arg_imm, arg_setup) = helpI arg in
         (ImmId(name, ()), arg_setup @ [(name, CPrim1(op, arg_imm, ()))])
      | EPrim2(op, left, right, tag) ->
         let name = sprintf "binop_%d" tag in
         let (left_imm, left_setup) = helpI left in
         let (right_imm, right_setup) = helpI right in
         (ImmId(name, ()), left_setup @ right_setup @ [(name, CPrim2(op, left_imm, right_imm, ()))])
      | EIf(cond, _then, _else, tag) ->
         let name = sprintf "if_%d" tag in
         let (cond_imm, cond_setup) = helpI cond in
         (ImmId(name, ()), cond_setup @ [(name, CIf(cond_imm, helpA _then, helpA _else, ()))])
      | EApp(funname, args, tag) ->
         let name = sprintf "func_%s_%d" funname tag in
         let (func_expr, setup) = helpC e in
         (ImmId(name, ()), setup @ [(name, func_expr)])
      | ELet([], body, _) -> helpI body
      | ELet((bind, exp, _)::rest, body, pos) ->
         let (exp_ans, exp_setup) = helpC exp in
         let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
         (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    in
    helpP p
;;

let r_to_asm (r : reg) : string =
  match r with
  | EAX -> "eax"
  | EDX -> "edx"
  | ESP -> "esp"
  | EBP -> "ebp"

let rec arg_to_asm (a : arg) : string =
  match a with
  | Const(n) -> sprintf "%d" n
  | HexConst(n) -> sprintf "0x%lx" (Int32.of_int n)
  | Reg(r) -> r_to_asm r
  | RegOffset(n, r) ->
     if n >= 0 then
       sprintf "[%s+%d]" (r_to_asm r) n
     else
       sprintf "[%s-%d]" (r_to_asm r) (-1 * n)
  | Sized(size, a) ->
     sprintf "%s %s"
         (match size with
             | DWORD_PTR -> "DWORD"
             | WORD_PTR -> "WORD"
             | BYTE_PTR -> "BYTE"
         )
         (arg_to_asm a)
;;

let rec i_to_asm (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
     sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd(dest, to_add) ->
     sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub(dest, to_sub) ->
     sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul(dest, to_mul) ->
     sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ICmp(left, right) ->
     sprintf "  cmp %s, %s" (arg_to_asm left) (arg_to_asm right)
  | ILabel(name) ->
     name ^ ":"
  | IJo(label) ->
     sprintf "  jo %s" label
  | IJe(label) ->
     sprintf "  je %s" label
  | IJne(label) ->
     sprintf "  jne %s" label
  | IJl(label) ->
     sprintf "  jl %s" label
  | IJle(label) ->
     sprintf "  jle %s" label
  | IJg(label) ->
     sprintf "  jg %s" label
  | IJge(label) ->
     sprintf "  jge %s" label
  | IJmp(label) ->
     sprintf "  jmp %s" label
  | IJz(label) ->
     sprintf "  jz %s" label
  | IJnz(label) ->
     sprintf "  jnz %s" label
  | IAnd(dest, value) ->
     sprintf "  and %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IOr(dest, value) ->
     sprintf "  or %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IXor(dest, value) ->
     sprintf "  xor %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShl(dest, value) ->
     sprintf "  shl %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShr(dest, value) ->
     sprintf "  shr %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ISar(dest, value) ->
     sprintf "  sar %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IPush(value) ->
     sprintf "  push %s" (arg_to_asm value)
  | IPop(dest) ->
     sprintf "  pop %s" (arg_to_asm dest)
  | ICall(label) ->
     sprintf "  call %s" label
  | IRet ->
     "  ret"
  | ITest(arg, comp) ->
     sprintf "  test %s, %s" (arg_to_asm arg) (arg_to_asm comp)
  | ILineComment(str) ->
     sprintf "  ;; %s" str
  | IInstrComment(instr, str) ->
     sprintf "%s ; %s" (i_to_asm instr) str

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
     if y = x then v else find rest x

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 1
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

(* Commonly used macros *)
let func_begin_label name = sprintf "%s_func_begin" name
let func_setup_label name = sprintf "%s_stack_setup_push_loop" name
let func_cleanup_label name = sprintf "%s_stack_cleanup_return" name

let rec arg_to_const arg = match arg with
    | Const(x) | HexConst(x) -> Some(x)
    | Sized(_, a) -> arg_to_const a
    | _ -> None

let check_bool arg label =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            [ IMov(Reg(EAX), arg); ]
        else
            [ IJmp(label); ]
    | _ ->
        [ IMov(Reg(EAX), arg);
          ITest(Reg(EAX), tag_as_bool);
          IJz(label); ]

let check_num arg label =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            [ IJmp(label); ]
        else
            [ IMov(Reg(EAX), arg); ]
    | _ ->
        [ IMov(Reg(EAX), arg);
          ITest(Reg(EAX), tag_as_bool);
          IJnz(label); ]

let check_logic arg = check_bool arg "err_LOGIC_NOT_BOOL"
let check_if arg = check_bool arg "err_IF_NOT_BOOL"
let check_arith arg = check_num arg "err_ARITH_NOT_NUM"
let check_compare arg = check_num arg "err_COMP_NOT_NUM"

let block_true_false label_true label_done = [
    IMov(Reg(EAX), const_false);
    IJmp(label_done);
    ILabel(label_true);
    IMov(Reg(EAX), const_true);
    ILabel(label_done);
]

let rec compile_fun (name : string) args env is_tail : instruction list =
    if is_tail then
        [   ILineComment(sprintf "Tail-call to function %s" name) ] @
            List.flatten (List.mapi
                (fun i a -> [ IMov(Reg(EAX), a); IMov(RegOffset(word_size*(i+2), EBP), Reg(EAX)); ])
                (List.rev_map (fun a -> compile_imm a env) args)) @
        [   IJmp(func_begin_label name) ]
    else
        [   ILineComment(sprintf "Call to function %s" name) ] @
            List.map
                (fun a -> IPush(Sized(DWORD_PTR, a)))
                (List.map (fun a -> compile_imm a env) args) @
        [   ICall(name);
            IAdd(Reg(ESP), Const((List.length args)*word_size)); ]
and compile_aexpr (e : tag aexpr) si env num_args is_tail : instruction list =
    match e with
    | ALet(name, exp, body, _) ->
        let setup = compile_cexpr exp si env num_args false in
        let arg = RegOffset(~-si*word_size, EBP) in
        let new_env = (name, arg)::env in
        let main = compile_aexpr body (si+1) new_env num_args true in
        setup @ [ IMov(arg, Reg(EAX)) ] @ main
    | ACExpr(e) ->
        compile_cexpr e si env num_args true
and compile_cexpr (e : tag cexpr) si env num_args is_tail : instruction list =
    match e with
    | CIf (cnd, thn, els, t) ->
        let label_false = sprintf "if_%d_false" t in
        let label_true = sprintf "if_%d_true" t in
        let label_done = sprintf "if_%d_done" t in
        let argCond = compile_imm cnd env in
        check_if argCond @ [
            (*IMov(Reg(EAX), argCond);*)
            ICmp(Reg(EAX), const_true);
            IJe(label_true);
            ICmp(Reg(EAX), const_false);
            IJe(label_false);
            IJmp("err_IF_NOT_BOOL");
            ILabel(label_true);
        ] @ compile_aexpr thn si env num_args true @ [
            IJmp(label_done);
            ILabel(label_false);
        ] @ compile_aexpr els si env num_args true @ [
            ILabel(label_done);
        ]
    | CPrim1(op, e, t) ->
        let arg = compile_imm e env in
        let label_true = sprintf "isboolnum_true_%d" t in
        let label_done = sprintf "isboolnum_done_%d" t in
        (match op with
        | Add1 ->
            check_arith arg @ [
            IAdd(Reg(EAX), Const(1 lsl 1));
            IJo("err_OVERFLOW");
        ]
        | Sub1 ->
            check_arith arg @ [
            ISub(Reg(EAX), Const(1 lsl 1));
            IJo("err_OVERFLOW");
        ]
        | Print -> [
            IMov(Reg(EAX), arg);
            IPush(Reg(EAX));
            ICall("print");
            IPop(Reg(EAX));
        ]
        | IsBool -> [
            IMov(Reg(EAX), arg);
            ITest(Reg(EAX), tag_as_bool);
            IJnz(label_true);
        ] @ block_true_false label_true label_done
        | IsNum -> [
            IMov(Reg(EAX), arg);
            ITest(Reg(EAX), tag_as_bool);
            IJz(label_true);
        ] @ block_true_false label_true label_done
        | Not ->
            check_logic arg @ [
            IXor(Reg(EAX), bool_mask);
        ]
        | PrintStack -> failwith "PrintStack not implemented"
        )
    | CPrim2(op, e1, e2, t) ->
        let label_true = sprintf "compare_%d_true" t in
        let label_done = sprintf "compare_%d_done" t in
        let arg1 = compile_imm e1 env in
        let arg2 = compile_imm e2 env in
        let prelude = match op with
            | Plus | Minus | Times ->
                check_arith arg2 @ check_arith arg1
            | Greater | GreaterEq | Less | LessEq | Eq ->
                check_compare arg2 @ check_compare arg1
            | And | Or ->
                check_logic arg2 @ check_logic arg1
        in prelude @ (match op with
        (* A lot of optimization here so watch out for bugs *)
        | Plus -> [
            IAdd(Reg(EAX), arg2);
            IJo("err_OVERFLOW");
        ]
        | Minus -> [
            ISub(Reg(EAX), arg2);
            IJo("err_OVERFLOW");
        ]
        | Times -> [
            IMul(Reg(EAX), arg2);
            IJo("err_OVERFLOW");
            ISar(Reg(EAX), Const(1));
        ]
        | And -> [
            IAnd(Reg(EAX), arg2);
        ]
        | Or -> [
            IOr(Reg(EAX), arg2);
        ]
        | Greater -> [
            ICmp(Reg(EAX), arg2);
            IJg(label_true);
        ] @ block_true_false label_true label_done
        | GreaterEq -> [
            ICmp(Reg(EAX), arg2);
            IJge(label_true);
        ] @ block_true_false label_true label_done
        | Less -> [
            ICmp(Reg(EAX), arg2);
            IJl(label_true);
        ] @ block_true_false label_true label_done
        | LessEq -> [
            ICmp(Reg(EAX), arg2);
            IJle(label_true);
        ] @ block_true_false label_true label_done
        | Eq -> [
            ICmp(Reg(EAX), arg2);
            IJe(label_true);
        ] @ block_true_false label_true label_done
        )
    | CApp(name, args, t) ->
        compile_fun name args env (is_tail && (num_args = List.length args))
    | CImmExpr(e) ->
        [ IMov(Reg(EAX), compile_imm e env) ]
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const((n lsl 1))
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> find env x

let func_stack_setup func_name stack_size = [
    ILabel(func_name);
    ILineComment(sprintf "Function %s: Stack setup" func_name);
    IPush(Reg(EBP));
    IMov(Reg(EBP), Reg(ESP));
    IMov(Reg(EAX), Reg(ESP));
    ISub(Reg(EAX), Const(stack_size));
    ILabel(func_setup_label func_name);
    IPush(Const(0));
    ICmp(Reg(EAX), Reg(ESP));
    IJne(func_setup_label func_name);
    ILabel(func_begin_label func_name);
    ILineComment(sprintf "Function %s starts here" func_name);
]

let func_stack_cleanup func_name stack_size = [
    ILineComment(sprintf "Function %s: Stack cleanup" func_name);
    ILabel(func_cleanup_label func_name);
    IAdd(Reg(ESP), Const(stack_size));
    IPop(Reg(EBP));
    IRet;
]

let compile_decl (d : tag adecl) : instruction list =
    match d with
    | ADFun(func_name, args_list, body, _) ->
    let stack_size = word_size * count_vars body in
    let (env, _) = List.fold_left
        (fun (ls, offset) name -> ((name, RegOffset(offset*word_size, EBP))::ls, offset+1))
        ([], 2) (* Starts at 2 because first arg is at ebp-8 *)
        (args_list)
    in  func_stack_setup func_name stack_size @
        compile_aexpr body 1 env (List.length args_list) true @
        func_stack_cleanup func_name stack_size

let rec optimize (ls : instruction list) =
    match ls with
    | [] -> []
    | (IMov(RegOffset(o1, r1), Reg(EAX)))::(IMov(Reg(EAX), RegOffset(o2, r2)))::rest ->
        if o1 = o2 && r1 = r2 then
            (List.hd ls)::optimize rest
        else
            (List.nth ls 0)::(List.nth ls 1)::optimize rest
    | what::rest ->
        what::optimize rest

let compile_prog (anfed : tag aprogram) =
    match anfed with | AProgram(decls, expr, _) ->
    let func_name = "our_code_starts_here" in
    let stack_size = word_size * (count_vars expr) in
    let to_string ls = List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" ls in
    let header =
"section .text
extern error
extern print
global our_code_starts_here" in
    let setup = func_stack_setup func_name stack_size in
    let cleanup = func_stack_cleanup func_name stack_size in
    let postlude = [
        (* Error handling labels *)
        ILineComment("Error handling labels - will not return!");
        ILabel("err_COMP_NOT_NUM");
        IPush(err_COMP_NOT_NUM);
        ICall("error");
        ILabel("err_ARITH_NOT_NUM");
        IPush(err_ARITH_NOT_NUM);
        ICall("error");
        ILabel("err_LOGIC_NOT_BOOL");
        IPush(err_LOGIC_NOT_BOOL);
        ICall("error");
        ILabel("err_IF_NOT_BOOL");
        IPush(err_IF_NOT_BOOL);
        ICall("error");
        ILabel("err_OVERFLOW");
        IPush(err_OVERFLOW);
        ICall("error");
    ] in
    let funcs = List.flatten(List.map (compile_decl) (decls)) in
    let main = compile_aexpr expr 1 [] 0 false in
    let text = to_string (optimize (funcs @ setup @ main @ cleanup @ postlude)) in
    header ^ text

let compile_to_string prog : (exn list, string) either =
  let errors = well_formed prog in
  match errors with
  | [] ->
     let tagged : tag program = tag prog in
     let anfed : tag aprogram = atag (anf tagged) in
     (* printf "Prog:\n%s\n" (ast_of_expr prog); *)
     (* printf "Tagged:\n%s\n" (format_expr tagged string_of_int); *)
     (* printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int); *)
     Right(compile_prog anfed)
  | _ -> Left(errors)
