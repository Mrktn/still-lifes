let N = 5;;
let k = 1 lsl N;;
let u = k * (k-1);;

(* Calcule le k-ième bit de n *)
let bit k n = (n lsr k) land 1;;

(* Si n et m codent 2 sommets du premier graphe, a-t-on chevauchement de n et m (dans cet ordre) ? *)
let overlap1 n m = ((bit 4 n) = (bit 5 m)) && ((bit 2 n) = (bit 3 m)) && ((bit 0 n) = (bit 1 m));;

let b2i b = if b then 1 else 0;;

let match1 n m = let etat = bit 2 n in
 let neigh = (bit 5 n) + (bit 4 n) + (bit 3 n) + (bit 1 n) + (bit 0 n) + (bit 4 m) + (bit 2 m) + (bit 0 m) in
 
 match etat with
  | 0 -> b2i ((neigh <> 3) && (overlap1 n m))
  | _ -> b2i (((neigh = 2) || (neigh = 3)) && (overlap1 n m));;

(* Lance la recherche des cycles sur le graphe en connaissant ses noeuds et la fonction qui à deux noeuds indique s'ils sont en relation *)
let find noeuds mtch = let k = vect_length noeuds in
   (* Z[i][p] : existe-t-il au moins un chemin du noeud n°i au noeud 0, de longueur p ? *)
      let Z = make_matrix k (N + 4) true
      
      (* M sera la matrice d'adjacence en construction (on ne la calcule qu'au moment d'explorer l'arête car le calcul est coûteux : c'est un O(N) au pire *)
      (* -1: pas encore calculé. 0: pas d'arête. 1: arête *)
      and M = make_matrix k k (-1) in
         let ret = ref [] in
            for j = 1 to (k - 1) do
               Z.(j).(1) <- false
            done;

            (* Lance un parcours de profondeur p du noeud n°i au noeud 0, en ayant suivi le chemin curr. Retourne vrai ssi au moins un chemin valide existe (pour s'économiser des appels ultérieurs *)
            let rec aux i p curr = match p with
               (* Il suffit d'ajouter curr à la liste si on est revenu en 0, et de conclure négativement sinon *)
               | 1 ->
                  if i = 0 then begin
                        ret := (rev curr) :: !ret;
                        true
                     end
                  else
                     false
               | _ -> let z = ref false in

                  (* Pour chaque noeud *)
                     for j = 0 to (k - 1) do
                        (* Si l'on ne risque pas de rencontrer un cul-de-sac... *)
                        if Z.(j).(p - 1) then
                           
                           match M.(i).(j) with
                           (* Si on n'a pas encore calculé M.(i).(j), on le calcule et on explore si c'est une arête *)
                           | (-1) -> let m = mtch noeuds.(i) noeuds.(j) in
                                 M.(i).(j) <- m;
                                 if (m = 1) then
                                    z := (aux j (p - 1) (noeuds.(j) :: curr)) || !z;

                           (* Sinon, si M.(i).(j) est calculé et s'il y a bien une arête *)
                           | _ -> if (M.(i).(j) = 1) then
                                 z := (aux j (p - 1) (noeuds.(j) :: curr)) || !z

                     done;
                     (* Au moins un chemin de i à 0 de longueur p existe si et seulement si au moins un des parcours de profondeur p-1 s'est avéré fructueux. *)
                     Z.(i).(p) <- !z;
                     !z;
            in

               aux 0 (N + 3) [0]; !ret;;


(* Est-ce que n chevauche m en tant que sommets du second graphe ?
   On a recours à des constantes magiques qui permettent de sélectionner les bons bits en temps constant : u et k *)
let overlap2 n m = ((n land u) lsr N) = (m land (k - 1));;

(* Une cellule dans l'état "state" reste-t-elle invariante quand elle possède "neighbours" voisines selon les règles du Jeu de la Vie ? *)
let invariant state neighbours = match state with
   | 0 -> neighbours <> 3
   | _ -> (neighbours = 2) || (neighbours = 3);;

(* A-t-on n->m dans le second graphe ? *)
let match2 n m = let ret = ref (overlap2 n m) in (* il faut : chevauchement des demi-cycles... *)

      (* ... et que la case blanche de gauche de la bordure reste invariante... *)
      ret := !ret && (((bit 0 n) + (bit N n) + (bit N m)) <> 3);
      
      (* ... pareil pour la case de droite... *)
      ret := !ret && (((bit (N - 1) n) + (bit (N - 1) m) + (bit (2 * N - 1) m)) <> 3);
      
      (* ... et que la 0ième reste invariante... *)
      ret := !ret && (invariant (bit 0 m) ((bit 0 n) + (bit 1 n) + (bit 1 m) + (bit N m) + (bit (N + 1) m)));

      (* ... et que les N-2 suivantes aussi... *)
      let i = ref 1 in
         while !ret && !i < (N - 1) do
            let neigh = (bit (!i - 1) n) + (bit !i n) + (bit (!i + 1) n) + (bit (N + !i - 1) m) + (bit (N + !i) m) + (bit (N + 1 + !i) m) + (bit (!i + 1) m) + (bit (!i - 1) m) in
               ret := (invariant (bit !i m) neigh);
               i := !i + 1
         done;
         
         (* ... et enfin que la N-1 ième soit aussi invariante *)
         b2i (!ret && (invariant (bit (N - 1) m) ((bit (N - 1) n) + (bit (N - 2) n) + (bit (N - 2) m) + (bit (2 * N - 2) m) + (bit (2 * N - 1) m))));;

(* Insère x dans la liste triée l s'il n'est pas déjà présent *)
let rec insere x l = match l with
   | [] -> [x]
   | y :: q -> if x < y then x :: l
      else if x = y then l
      else y :: (insere x q);;

(* Coupe une suite de sommets (codant un cycle valide dans le premier graphe) en 2 demi-cycles *)
let split l = let up = ref 0 and down = ref 0 in
      let v = vect_of_list l in
         for k = 0 to (N - 1) do
            let a = (bit 4 v.(k)) and b = (bit 2 v.(k)) and c = (bit 0 v.(k)) in
               up := !up + (a * (1 lsl (k))) + (b * (1 lsl (N + k)));
               down := !down + (b * (1 lsl (k))) + (c * (1 lsl (N + k)));
         done; (!up, !down);;

let nodes1 = make_vect 64 0;;
for i = 1 to 63 do
   nodes1.(i) <- i
done;;

let suites = ref (map tl (find nodes1 match1)) in
   let demicycles = ref [] in

      (* On procède ainsi pour éviter d'avoir deux fois le même noeud dans le second graphe *)
      while !suites <> [] do
         let h = hd !suites in
            suites := tl !suites;
            let (u, d) = split h in
               demicycles := insere u (!demicycles);
               demicycles := insere d (!demicycles)
      done;

      (* Ici demicycles contient nos noeuds d'ordre 2. Il ne reste qu'à lancer une recherche de cycles. *)
      find (vect_of_list !demicycles) match2;;

