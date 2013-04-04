(* naive: no elements, not O(1) *)

module Deque : sig
  type t

  val empty : t

  val push : t -> t
  val pop : t -> t

  val inject : t -> t
  val eject : t -> t

  val print : t -> unit
end = struct
  module Color = struct
    type t = Green | Red | Yellow

    let from_int = function
      | 0 | 5 -> Red
      | 1 | 4 -> Yellow
      | 2 | 3 -> Green
      | _ -> assert false

    let to_string = function
      | Red -> "R"
      | Yellow -> "Y"
      | Green -> "G"

    let min a b = match a, b with
      | Red, _ | _, Red -> Red
      | Yellow, _ | _, Yellow -> Yellow
      | _, _ -> Green
  end

  module Lvl = struct
    type t = int * int

    let empty = (0, 0)

    let color = function
      | 0, n | n, 0 -> Color.from_int n
      | m, n -> Color.(min (from_int m) (from_int n))
  end

  type t = Lvl.t list

  let two_buff_case (pi, si) (pSi, sSi) =
    let (pSi, sSi) = if pSi = 0 then (1, sSi - 1) else pSi, sSi in
    let (pSi, sSi) = if sSi = 0 then (pSi - 1, 1) else pSi, sSi in
    let (pi, pSi) =
      if pi >= 4 then
        (pi - 2, pSi + 1)
      else if pi <= 1 then
        (pi + 2, pSi - 1)
      else
        pi, pSi
    in
    let (si, sSi) =
      if si >= 4 then
        (si - 2, sSi + 1)
      else if si <= 1 then
        (si + 2, sSi - 1)
      else
        si, sSi
    in
    (pi, si), (match pSi, sSi with 0, 0 -> None | _ -> Some (pSi, sSi))

  let one_buff_case (pi, si) (pSi, sSi) =
    let pSi = max pSi sSi in
    let (pi, pSi) =
      if pi >= 4 then
        (pi - 2, pSi + 1)
      else if pi <= 1 then
        (pi + 2, pSi - 1)
      else
        pi, pSi
    in
    let (si, pSi) =
      if si >= 4 then
        (si - 2, pSi + 1)
      else if si <= 1 then
        (si + 2, pSi - 1)
      else
        si, pSi
    in
    (pi, si), (if pSi = 0 then None else Some (pSi, 0))

  let no_buff_case (pi, si) (pSi, sSi) =
    let pi = max pi si in
    let pi = if pSi + sSi = 1 then pi + 2 else pi in
    (pi, 0), None

  let do_regularize ((pi, si) as lvli) ((pSi, sSi) as lvlSi) =
    if pSi + sSi >= 2 then
      two_buff_case lvli lvlSi
    else if pi >= 2 || si >= 2 then
      one_buff_case lvli lvlSi
    else
      no_buff_case lvli lvlSi

  let rec regularize = function
    | [] -> []
    | lvl :: rest when Lvl.color lvl <> Color.Red -> lvl :: regularize rest
    | lvli :: lvlSi :: rest ->
      begin match do_regularize lvli lvlSi, rest with
      | (lvl, None), [] -> [lvl]
      | (lvli, Some lvlSi), rest -> lvli :: lvlSi :: rest
      | _, _ -> assert false
      end
    | [ last_lvl ] ->
      begin match do_regularize last_lvl Lvl.empty with
      | (lvl, None) -> [lvl]
      | (lvli, Some lvlSi) -> [ lvli ; lvlSi ]
      end

  let empty = [0, 0]

  let dirty_push = function
    | [] -> assert false
    | (prefix, suffix) :: lvls -> (succ prefix, suffix) :: lvls

  let push x = regularize (dirty_push x)

  let dirty_pop = function
    | [] -> assert false
    | (prefix, suffix) :: lvls -> (pred prefix, suffix) :: lvls

  let pop x = regularize (dirty_pop x)

  let dirty_inject = function
    | [] -> assert false
    | (prefix, suffix) :: lvls -> (prefix, succ suffix) :: lvls

  let inject x = regularize (dirty_inject x)

  let dirty_eject = function
    | [] -> assert false
    | (prefix, suffix) :: lvls -> (prefix, succ suffix) :: lvls

  let eject x = regularize (dirty_eject x)

  let print lst =
    let aux i ((p, s) as lvl) =
      Printf.printf "%dth lvl (%s) : | %d , %d |\n"
        i (Color.to_string (Lvl.color lvl)) p s
    in
    List.iteri aux lst
end
