open Why3

type error = Exn of (Loc.position option * exn)
type 'a iresult = ('a, error list) Result.t

let return = Result.ok
let error (e : error) : 'a iresult = Result.error [ e ]

let error_with ?loc msg =
  Format.kasprintf (fun s -> error @@ Exn (loc, Failure s)) msg

let error_of_fmt ?loc msg = Format.kasprintf (fun s -> Exn (loc, Failure s)) msg

let trace ~(err : error) (m : 'a iresult) : 'a iresult =
  match m with Ok v -> return v | Error tr -> Error (err :: tr)

let error_unless (b : bool) ~(err : error) : unit iresult =
  if b then return () else error err

let ( >>= ) = Result.bind
let ( let* ) = Result.bind

let raise_error (m : 'a iresult) : 'a =
  let rec fmt_trace ?loc tr =
    match tr with
    | [] -> assert false
    | [ Exn (None, e) ] -> Loc.error ?loc e
    | [ Exn (Some loc, e) ] -> Loc.error ~loc e
    | Exn (None, _) :: tl -> fmt_trace ?loc tl
    | Exn (Some loc, _) :: tl -> fmt_trace ~loc tl
  in
  match m with Ok v -> v | Error tr -> fmt_trace tr

module StringMap = struct
  include Map.Make (String)

  let fold_e (f : key -> 'a -> 'b -> 'b iresult) (m : 'a t) (acc : 'b) :
      'b iresult =
    fold
      (fun k e acc ->
        let* acc = acc in
        f k e acc)
      m (return acc)
end

module Option = struct
  include Option

  let to_iresult (o : 'a option) ~(none : error) : 'a iresult =
    match o with Some v -> return v | None -> error none
end

module List = struct
  include List

  let fold_left_e (f : 'a -> 'b -> 'a iresult) (acc : 'a) (l : 'b list) =
    fold_left
      (fun acc x ->
        let* acc = acc in
        f acc x)
      (return acc) l

  let map_e (f : 'a -> 'b iresult) (l : 'a list) : 'b list iresult =
    let* l =
      fold_left_e
        (fun tl x ->
          let* x = f x in
          return @@ (x :: tl))
        [] l
    in
    return @@ List.rev l
end
