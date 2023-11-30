open Why3
open Ptree

type mapper = {
  ident : ident -> ident;
  qualid : mapper -> qualid -> qualid;
  pty : mapper -> pty -> pty;
  pattern : mapper -> pattern -> pattern;
  term : mapper -> term -> term;
}

let default_mapper =
  let ident id = id in
  let qualid sub qid =
    match qid with
    | Qident id -> Qident (sub.ident id)
    | Qdot (qid, id) -> Qdot (sub.qualid sub qid, sub.ident id)
  in
  let pty sub pty =
    match pty with
    | PTtyvar id -> PTtyvar (sub.ident id)
    | PTtyapp (qid, ptys) ->
        PTtyapp (sub.qualid sub qid, List.map (sub.pty sub) ptys)
    | PTtuple ptys -> PTtuple (List.map (sub.pty sub) ptys)
    | PTref ptys -> PTtuple (List.map (sub.pty sub) ptys)
    | PTarrow (pty1, pty2) -> PTarrow (sub.pty sub pty1, sub.pty sub pty2)
    | PTscope (qid, pty) -> PTscope (sub.qualid sub qid, sub.pty sub pty)
    | PTparen pty -> PTparen (sub.pty sub pty)
    | PTpure pty -> PTpure (sub.pty sub pty)
  in
  let pattern sub pat =
    let pat_desc =
      match pat.pat_desc with
      | Pwild -> Pwild
      | Pvar id -> Pvar (sub.ident id)
      | Papp (qid, pats) ->
          Papp (sub.qualid sub qid, List.map (sub.pattern sub) pats)
      | Prec flds ->
          Prec
            (List.map
               (fun (qid, pat) -> (sub.qualid sub qid, sub.pattern sub pat))
               flds)
      | Ptuple pats -> Ptuple (List.map (sub.pattern sub) pats)
      | Pas (pat, id, ghost) -> Pas (sub.pattern sub pat, sub.ident id, ghost)
      | Por (pat1, pat2) -> Por (sub.pattern sub pat1, sub.pattern sub pat2)
      | Pcast (pat, pty) -> Pcast (sub.pattern sub pat, sub.pty sub pty)
      | Pscope (qid, pat) -> Pscope (sub.qualid sub qid, sub.pattern sub pat)
      | Pparen pat -> Pparen (sub.pattern sub pat)
      | Pghost pat -> Pghost (sub.pattern sub pat)
    in
    { pat with pat_desc }
  in
  let term sub term =
    let term_desc =
      match term.term_desc with
      | Ttrue -> Ttrue
      | Tfalse -> Tfalse
      | Tconst c -> Tconst c
      | Tident qid -> Tident (sub.qualid sub qid)
      | Tasref qid -> Tasref (sub.qualid sub qid)
      | Tidapp (qid, ts) ->
          Tidapp (sub.qualid sub qid, List.map (sub.term sub) ts)
      | Tapply (t1, t2) -> Tapply (sub.term sub t1, sub.term sub t2)
      | Tinfix (t1, id, t2) ->
          Tinfix (sub.term sub t1, sub.ident id, sub.term sub t2)
      | Tinnfix (t1, id, t2) ->
          Tinnfix (sub.term sub t1, sub.ident id, sub.term sub t2)
      | Tbinop (t1, bop, t2) -> Tbinop (sub.term sub t1, bop, sub.term sub t2)
      | Tbinnop (t1, bop, t2) -> Tbinnop (sub.term sub t1, bop, sub.term sub t2)
      | Tnot t -> Tnot (sub.term sub t)
      | Tif (t1, t2, t3) ->
          Tif (sub.term sub t1, sub.term sub t2, sub.term sub t3)
      | Tquant (qop, binds, trig, t) ->
          Tquant
            (qop, binds, List.map (List.map (sub.term sub)) trig, sub.term sub t)
      | Teps (id, pty, t) -> Teps (sub.ident id, sub.pty sub pty, sub.term sub t)
      | Tattr (attr, t) -> Tattr (attr, sub.term sub t)
      | Tlet (id, t1, t2) ->
          Tlet (sub.ident id, sub.term sub t1, sub.term sub t2)
      | Tcase (t, cls) ->
          Tcase
            ( sub.term sub t,
              List.map
                (fun (pat, t) -> (sub.pattern sub pat, sub.term sub t))
                cls )
      | Tcast (t, pty) -> Tcast (sub.term sub t, sub.pty sub pty)
      | Ttuple ts -> Ttuple (List.map (sub.term sub) ts)
      | Trecord flds ->
          Trecord
            (List.map
               (fun (qid, t) -> (sub.qualid sub qid, sub.term sub t))
               flds)
      | Tupdate (t, flds) ->
          Tupdate
            ( sub.term sub t,
              List.map
                (fun (qid, t) -> (sub.qualid sub qid, sub.term sub t))
                flds )
      | Tscope (qid, t) -> Tscope (sub.qualid sub qid, sub.term sub t)
      | Tat (t, id) -> Tat (sub.term sub t, sub.ident id)
    in
    { term with term_desc }
  in
  { ident; qualid; pty; pattern; term }

let apply_term (t : term) (mapper : mapper) : term = mapper.term mapper t
