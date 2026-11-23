module

public import Development.EtaleCohomology.TateTwists.Bundle0001
public import Development.EtaleCohomology.KummerTheory.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibnizOfPairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW

namespace LateralTheory.EtaleFoundations.AWLeib
variable {R : Type} [CommRing R]

theorem bd_map {E : Spc} {U : Scheme.{0}} {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    (f : ∀ p : ℕ, Sx E p U → G) (p : ℕ) (y : Sx E p U) : φ (bd f p y) = bd (fun q z => φ (f q z)) p y := by
  cases p with
  | zero => simp [bd]
  | succ p => simp [bd, map_sum, map_zsmul]

theorem ev_delta_bd {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ)
    (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (δ n m α) p t ht U x = Sec.map (I.d s t) (ev (R := R) α p s hs U x) +
      m.negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = t then ev (R := R) α q t hh U z else 0) p x := by
  have ev_eq {k : ℤ} (a : Cochain ((chains R).obj E) I k) (q : ℕ) (j : ℤ)
      (h : -(q : ℤ) + k = j) (y : Sx E q U) :
      ev (R := R) a q j h U y = Sec.map ((chainsXIso R E q).inv ≫ a.v _ _ h) (freeGen R _ U y) := rfl
  cases p with
  | zero =>
    rw [ev_eq, δ_v n m hm α _ _ ht s 1 (by omega) (by simp),
      (isZero_pos E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0]
    simp only [zero_comp, smul_zero, add_zero, bd]
    rfl
  | succ p =>
    have hp : -(p : ℤ) + n = t := by omega
    rw [ev_eq, δ_v n m hm α _ _ ht s (-(p : ℤ)) (by omega) (by omega),
      Preadditive.comp_add, Linear.comp_units_smul, reassoc_of% (chains_d (R := R) E p),
      Preadditive.sum_comp]
    refine (sec_map_add _ _ _).trans ?_
    congr 1
    rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
    congr 1
    simp only [bd, dite_eq_left hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, sec_map_zsmul, ev_eq]
    congr 1
    exact congrArg (Sec.map ((chainsXIso R E p).inv ≫ α.v (-(p : ℤ)) t hp)) (map_freeGen (E.δ i) U x)

theorem mul_congr {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w) (h' : s' + t' = w) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    μ.mul U s t w h (ev (R := R) α p s hs U y) (ev (R := R) β q t ht U z) =
      μ.mul U s' t' w h' (ev (R := R) α p s' hs' U y) (ev (R := R) β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

theorem leib' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s')
    (ht : t + 1 = t') (hw : w + 1 = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' (by omega) (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst hs ht hw; exact μ.leibniz U s t w h a b

theorem mul_bd_left {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    μ.mul U s t w h (bd f p y) b = bd (fun q z => μ.mul U s t w h (f q z) b) p y :=
  bd_map (((μ.mul U s t w h).flip b).toAddMonoidHom) f p y

theorem mul_bd_right {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    μ.mul U s t w h a (bd f p y) = bd (fun q z => μ.mul U s t w h a (f q z)) p y :=
  bd_map ((μ.mul U s t w h a).toAddMonoidHom) f p y

theorem secmap_sum {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (s : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ s, f i) = ∑ i ∈ s, Sec.map φ (f i) := map_sum ((φ.hom.app (op U)).hom) f s

theorem secmap_zsmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_zsmul ((φ.hom.app (op U)).hom) c a

def Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w hh (ev (R := R) α p _ rfl U y) (ev (R := R) β q _ rfl U z) else 0

theorem recombine {G : Type*} [AddCommGroup G] (X Y BF BF' BB BB' : G) (c s K c' P e1 e2 c2 e3 : ℤ) (hF : BF' = BF)
    (hB : BB' = BB) (h2 : c * s = e2 * c2) (h3 : K * c' = c * e1) (h4 : K * (c * P) = e2 * (c2 * e3)) :
    c • (X + s • Y) + K • (c' • BF + c • P • BB) = c • (X + e1 • BF') + e2 • c2 • (Y + e3 • BB') := by
  subst hF hB
  simp only [smul_add, smul_smul]
  rw [h2, h3, h4]
  abel

theorem sign_nat (p : ℕ) : ((-1 : ℤ) ^ p) = (((p : ℤ).negOnePow : ℤˣ) : ℤ) := by
  simp [Int.negOnePow_def]

end LateralTheory.EtaleFoundations.AWLeib


open LateralTheory.EtaleFoundations.AWLeib in
theorem LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hγ h1 h2
  have ev_ext (a b : Cochain ((chains R).obj E) K (k + 1))
      (h : ∀ p s hs U x, ev (R := R) a p s hs U x = ev (R := R) b p s hs U x) : a = b := by
    ext i j hij : 1
    by_cases hi : 0 < i
    · exact (isZero_pos E i hi).eq_of_src _ _
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ (fun U x => h p j hij U x)
  apply ev_ext
  intro N w hw U x
  have ev_add : ev (R := R) (γ₁ + n.negOnePow • γ₂) N w hw U x =
      ev (R := R) γ₁ N w hw U x + ev (R := R) (n.negOnePow • γ₂) N w hw U x := by
    unfold ev
    rw [Cochain.add_v, Preadditive.comp_add]
    rfl
  have ev_units_smul : ev (R := R) (n.negOnePow • γ₂) N w hw U x = n.negOnePow • ev (R := R) γ₂ N w hw U x := by
    change Sec.map ((chainsXIso R E N).inv ≫ (n.negOnePow • γ₂).v _ _ hw) (freeGen R _ U x) = _
    rw [Cochain.units_smul_v, Linear.comp_units_smul, Units.smul_def, sec_map_zsmul]
    rfl
  rw [ev_add, ev_units_smul, ev_delta_bd rfl γ N (-(N : ℤ) + k) w rfl hw U x, hγ N _ rfl U x, h1 N w hw U x,
    h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fm μ α β U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dite_eq_left (by omega), hγ N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fm
    rw [dite_eq_left (by omega)]
  rw [bd_aw (Fm μ α β U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, leib' μ U _ _ _ (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) w _ (by ring) (by ring) (by omega)]
  rw [ev_delta_bd rfl α p (-((p : ℕ) : ℤ) + n) _ rfl _ U, ev_delta_bd rfl β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl _ U]
  simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Units.smul_def, mul_bd_left, mul_bd_right]
  refine recombine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    rw [dite_eq_left (by omega)]
    unfold Fm
    rw [dite_eq_left (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    rw [dite_eq_left (by omega)]
    unfold Fm
    rw [dite_eq_left (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-((p : ℕ) : ℤ), by ring⟩
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvB
variable {R : Type} [CommRing R]

theorem ev_add {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev]

noncomputable def evHom {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
  AddMonoidHom.mk' (fun α => ev α p s h U x) (fun α β => ev_add α β p s h U x)

theorem ev_compHom {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp [ev, Cochain.comp_v _ _ (add_zero n) _ s s h (add_zero s)]

theorem isZero_pos {E : Spc} (a : ℤ) (ha : 0 < a) : IsZero (((chains R).obj E).X a) := by
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  change -(j : ℤ) = a at hj
  omega

theorem free_ext {P : PSh} {F : Shv R} (φ ψ : (free R).obj P ⟶ F)
    (hφ : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := hφ U.unop x
  simp only [freeGen] at this
  exact this

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => ModuleCat.Hom.hom f y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) x :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom f y)
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem freeGen_map {P Q : PSh} (f : P ⟶ Q) U x :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have key := fun y => congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) y)
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  unfold freeGen
  refine ((key _).symm).trans ?_
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.whiskeringRight_obj_map, Functor.comp_map, Functor.whiskerRight_app, uliftFunctor_map] <;> try (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  all_goals simp [freeP, ModuleCat.freeMk, ModuleCat.free, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem chainsXIso_nat {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p:ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp [chainsXIso, chains, chainsN, HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f p = -(p:ℤ) from rfl)]
  erw [Iso.inv_hom_id_assoc]
  try rfl

theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have := sec_nat ((chainsXIso R E p).inv ≫ α.v _ _ h) g (freeGen R _ U x)
  rw [freeGen_res] at this
  exact this

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hαβ : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  apply Cochain.ext
  intro a b hab
  by_cases ha : 0 < a
  · exact (isZero_pos a ha).eq_of_src _ _
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -(k : ℤ) := ⟨(-a).toNat, by omega⟩
  rw [← cancel_epi (chainsXIso R E k).inv]
  exact free_ext _ _ (fun U x => hαβ k b hab U x)

theorem ev_pull {E E' : Spc} {I : Cx R} {n : ℤ} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  have e1 : ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)).v (-(p:ℤ)) s h =
      ((chains R).map f).f (-(p:ℤ)) ≫ α.v (-(p:ℤ)) s h := by
    rw [Cochain.comp_v _ _ (zero_add n) (-(p:ℤ)) (-(p:ℤ)) s (add_zero _) h, Cochain.ofHom_v]
  unfold ev
  rw [e1, ← Category.assoc, chainsXIso_nat, Category.assoc]
  have := freeGen_map (R := R) (f.app (op (SimplexCategory.mk p))) U x
  simp only [Sec.map] at this
  simp [this, Sx.map]

end LateralTheory.EtaleFoundations.EvB

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleCochainEvaluationLinear := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ?_, fun α p s h V U g x => LateralTheory.EtaleFoundations.EvB.ev_res α p s h V U g x,
    fun α β hαβ => LateralTheory.EtaleFoundations.EvB.ev_ext α β hαβ, fun f α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_pull f α p s h U x,
    fun m α p s h U x => LateralTheory.EtaleFoundations.EvB.ev_compHom m α p s h U x⟩
  have H := LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) (E := E) p s h U x
  exact ⟨map_add (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β, map_sub (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) α β,
    map_zero (LateralTheory.EtaleFoundations.EvB.evHom (I := I) (n := n) p s h U x), fun c => map_zsmul (LateralTheory.EtaleFoundations.EvB.evHom p s h U x) c α⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvDeltaPf

variable {R : Type} [CommRing R]

def secHom {F G : Shv R} (U : Scheme.{0}) (x : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := Sec.map φ x
  map_zero' := by simp [Sec.map]
  map_add' f g := by simp [Sec.map]

lemma sec_zsmul {F G : Shv R} (f : F ⟶ G) (c : ℤ) (U : Scheme.{0}) (x : Sec F U) : Sec.map (c • f) x = c • Sec.map f x :=
  map_zsmul (secHom (G := G) U x) c f

lemma sec_sum {ι : Type} (s : Finset ι) {F G : Shv R} (f : ι → (F ⟶ G)) (U : Scheme.{0}) (x : Sec F U) : Sec.map (∑ i ∈ s, f i) x = ∑ i ∈ s, Sec.map (f i) x :=
  map_sum (secHom (G := G) U x) f s

variable (R) in
lemma freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) : Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  calc _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := rfl
    _ = (((freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := by rw [toSheafify_naturality]
    _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) := rfl
    _ = _ := by
      unfold freeGen
      congr 1
      simp [freeP, ModuleCat.freeMk]
      exact Finsupp.mapDomain_single

variable (R) in
lemma chains_d (E : Spc) (p : ℕ) : (chainsXIso R E (p+1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (chainsXIso R E (p+1)).hom ≫ ((chainsN R).obj E).d (p+1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq _ _ rfl rfl
  have h2 : ((chainsN R).obj E).d (p+1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
    simp [chainsN]
  rw [h1, h2, Iso.inv_hom_id_assoc]
  rfl

variable (R) in
lemma etale_simplicial_chains_isZero_of_positive_degree (E : Spc) (k : ℤ) (hk : 0 < k) : IsZero (((chains R).obj E).X k) :=
  HomologicalComplex.isZero_extend_X _ _ _ (by rintro i (h : -(i:ℤ) = k); omega)

lemma sec_add {F G : Shv R} (f g : F ⟶ G) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
  map_add (secHom (G := G) U x) f g

lemma sec_comp {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem part0 {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (x : Sx E 0 U) : ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
  have hz : ((chains R).obj E).d (-((0:ℕ):ℤ)) (-((0:ℕ):ℤ) + 1) = 0 := (etale_simplicial_chains_isZero_of_positive_degree R E _ (by omega)).eq_of_tgt _ _
  have key : (chainsXIso R E 0).inv ≫ (δ n m α).v (-((0:ℕ):ℤ)) m (by simp) = ((chainsXIso R E 0).inv ≫ α.v (-((0:ℕ):ℤ)) n (by simp)) ≫ I.d n m := by
    rw [δ_v n m hm α _ _ (by simp) n (-((0:ℕ):ℤ) + 1) (by omega) rfl, hz]
    simp
  show Sec.map (_ ≫ _) _ = _
  rw [key]
  rfl

theorem partS {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) : ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  have key : (chainsXIso R E (p+1)).inv ≫ (δ n m α).v _ t ht = ((chainsXIso R E (p+1)).inv ≫ α.v _ s hs) ≫ I.d s t + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((free R).map (E.δ i) ≫ ((chainsXIso R E p).inv ≫ α.v (-(p:ℤ)) t (by omega))) := by
    rw [δ_v n m hm α _ _ ht s (-(p:ℤ)) (by omega) (by push_cast; ring), Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ← Category.assoc, chains_d]
    simp only [Category.assoc, Preadditive.sum_comp, Linear.smul_comp]
  show Sec.map (_ ≫ _) _ = _
  rw [key, Units.smul_def, Units.smul_def, sec_add, sec_zsmul, sec_sum]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [sec_zsmul, sec_comp, freeGen_map]
  rfl

end LateralTheory.EtaleFoundations.EvDeltaPf

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds : LateralTheory.EtaleFoundations.EtaleCochainEvaluationCoboundaryFormula := by
  intro R _ E I n m hm α U
  exact ⟨fun x => LateralTheory.EtaleFoundations.EvDeltaPf.part0 hm α U x,
    fun p s t hs ht x => LateralTheory.EtaleFoundations.EvDeltaPf.partS hm α U p s t hs ht x⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable (R : Type) [CommRing R]

noncomputable def psiOf (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift.{1} (P.obj U) => a U.unop x.down)
  naturality := by
    intro U V g
    refine ModuleCat.free_hom_ext (fun x => ?_)
    have := ha V.unop U.unop g.unop x.down
    simp [freeP] at this ⊢
    exact this.symm

theorem free_hom_exists (P : PSh) (F : Shv R) (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x := by
  let ψ := psiOf R P F a ha
  let φ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj ((freeP R).obj P) ⟶ F :=
    ((sheafificationAdjunction _ _).homEquiv _ _).symm ψ
  have key : toSheafify _ ((freeP R).obj P) ≫ φ.hom = ψ := by
    have := ((sheafificationAdjunction _ _).homEquiv _ _).apply_symm_apply ψ
    rw [Adjunction.homEquiv_unit] at this
    exact this
  refine ⟨φ, fun U x => ?_⟩
  change ((toSheafify _ ((freeP R).obj P)).app (op U) ≫ φ.hom.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = _
  rw [← NatTrans.comp_app, key]
  erw [ModuleCat.freeDesc_apply]
  rfl

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  intro R _ E I n a ha
  have hex : ∀ (p : ℕ) (s : ℤ) (h : -(p:ℤ) + n = s), ∃ φ : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s,
      ∀ U x, Sec.map φ (freeGen R _ U x) = a p s h U x :=
    fun p s h => free_hom_exists R _ _ (a p s h) (fun V U g x => ha p s h V U g x)
  choose φ hφ using hex
  let f : ∀ (p : ℕ) (s : ℤ) (_ : -(p:ℤ) + n = s), (((chains R).obj E).X (-(p:ℤ)) ⟶ I.X s) :=
    fun p s h => (chainsXIso R E p).hom ≫ φ p s h
  let α : Cochain ((chains R).obj E) I n := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫ f (-i).toNat j (by omega)
    else 0)
  refine ⟨α, fun p s h U x => ?_⟩
  have gen : ∀ (q : ℕ) (hq : q = p) (e : -(p:ℤ) = -(q:ℤ)) (h' : -(q:ℤ) + n = s),
      (((chains R).obj E).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
    rintro q rfl e h'
    simp
  have hv : α.v (-(p:ℤ)) s h = f p s h := by
    simp only [α, Cochain.mk_v]
    rw [dite_eq_left (by omega)]
    exact gen _ (by omega) _ _
  simp only [GlobalTheory.EtC.ev]
  rw [hv]
  simp only [f]
  rw [Iso.inv_hom_id_assoc]
  exact hφ p s h U x
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCochainCupAssocOfCupSpecAndAlexanderWhitney
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_cup_spec0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def t_aw_assoc0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M')
    (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w)
      (h3 : t + u = tu) (h4 : s + tu = w) a b c,
      ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
    ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
      (ab : Cochain ((chains R).obj E) M nm) (bc : Cochain ((chains R).obj E) M' mk)
      (x y : Cochain ((chains R).obj E) L w),
      μ.IsAW h1 α β ab → ν.IsAW h2 ab γ x → μ'.IsAW h3 β γ bc → ν'.IsAW h4 α bc y → x = y

theorem etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc (hs : t_cup_spec0) (ha : t_aw_assoc0) : EtaleCochainCupAssociativeOfPairing := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨ab, hab⟩ := (hs R μ (E := E) h1).1 α β
  rw [(hs R μ (E := E) h1).2 α β ab hab]
  obtain ⟨x, hx⟩ := (hs R ν (E := E) h2).1 ab γ
  rw [(hs R ν (E := E) h2).2 ab γ x hx]
  obtain ⟨bc, hbc⟩ := (hs R μ' (E := E) h3).1 β γ
  rw [(hs R μ' (E := E) h3).2 β γ bc hbc]
  obtain ⟨y, hy⟩ := (hs R ν' (E := E) h4).1 α bc
  rw [(hs R ν' (E := E) h4).2 α bc y hy]
  congr 1
  exact Subtype.ext (ha R μ ν μ' ν' hass E h1 h2 h3 h4 α.1 β.1 γ.1 ab.1 bc.1 x.1 y.1 hab hx hbc hy)

end LateralTheory.EtaleFoundations
end

