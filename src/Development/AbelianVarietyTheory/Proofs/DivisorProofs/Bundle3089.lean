module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisTangentModuleLocalizedAbelianLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDlogAddCoboundaryAbLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.CechH1Local

theorem isCob_of_refine_le {Y : Scheme.{0}} {I K : Type} (Uc : I → Y.Opens) (c : C1 Uc) (hc : IsCoc Uc c)
    (V : K → Y.Opens) (σ : K → I) (hV : ∀ p, V p ≤ Uc (σ p)) (hVt : ∀ i, Uc i ≤ ⨆ p, V p)
    (B : ∀ p, Γ(Y, V p)) (hB : ∀ p p', rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      rsT (B p') (V p ⊓ V p') - rsT (B p) (V p ⊓ V p')) : IsCob Uc c := by
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, V p → O ≤ ⨆ p, O ⊓ V p := by
    intro O hO x hx
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hO hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have left {a b d : Y.Opens} (h : a ≤ d) : a ⊓ b ≤ d := inf_le_left.trans h
  have right {a b d : Y.Opens} (h : b ≤ d) : a ⊓ b ≤ d := inf_le_right.trans h
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _ (hVt i)) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    simp (disch := aesop (add safe apply [le_inf, inf_le_left, inf_le_right, left, right, hV])) only [rsT_rsT] at h1 h2 ⊢
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left)
    (cov _ (inf_le_left.trans (hVt i))) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  simp (disch := aesop (add safe apply [le_inf, inf_le_left, inf_le_right, left, right, hV])) only [rsT_rsT] at h1 h2 h3 ⊢
  linear_combination h1 - h2 + h3

theorem rsT_field {Z : Scheme.{0}} {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hd : IsField ⊤ d) {O O' : Z.Opens}
    (h : O' ≤ O) (f : Γ(Z, O)) : rsT (d O f) O' = d O' (rsT f O') := by
  rw [rsT_of_le h, rsT_of_le h, hd.2.2 _ _ h le_top]

theorem rsT_appLE {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (r : Γ(X, V)) : rsT ((π.appLE V O h).hom r) O' = (π.appLE V O' (h'.trans h)).hom r := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom r) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_unit {Z : Scheme.{0}} {T O : Z.Opens} (h : O ≤ T) (u : Γ(Z, T)ˣ) :
    rsT u.val O * rsT u⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem isCoc_dlg {Z : Scheme.{0}} (L : LB Z) (hL : L.IsLB) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField ⊤ d) {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hj : ∀ i, W i ≤ L.U (j i)) :
    IsCoc W (fun i i' => d (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
      rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) := by
  intro i i' i''
  set O := W i ⊓ W i' ⊓ W i''
  have l₁ : O ≤ W i ⊓ W i' := inf_le_left
  have l₂ : O ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : O ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have m₁ : W i ⊓ W i' ≤ L.U (j i) ⊓ L.U (j i') := inf_le_inf (hj i) (hj i')
  have m₂ : W i' ⊓ W i'' ≤ L.U (j i') ⊓ L.U (j i'') := inf_le_inf (hj i') (hj i'')
  have m₃ : W i ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i'') := inf_le_inf (hj i) (hj i'')
  have k : ∀ (a b : J) (l : O ≤ W a ⊓ W b) (m : W a ⊓ W b ≤ L.U (j a) ⊓ L.U (j b)),
      rsT (d (W a ⊓ W b) (rsT (L.g (j a) (j b)).val (W a ⊓ W b)) * rsT (L.g (j a) (j b))⁻¹.val (W a ⊓ W b)) O =
        d O (rsT (L.g (j a) (j b)).val O) * rsT (L.g (j a) (j b))⁻¹.val O := by
    intro a b l m
    rw [rsT_mul, rsT_field hd l, rsT_rsT m l, rsT_rsT m l]
  rw [k i i' l₁ m₁, k i' i'' l₂ m₂, k i i'' l₃ m₃]
  have T3 : O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    le_inf (le_inf (l₁.trans (m₁.trans inf_le_left)) (l₁.trans (m₁.trans inf_le_right)))
      (l₂.trans (m₂.trans inf_le_right))
  have co := congrArg (fun u => rsT (Units.val u) O) (hL.cocycle (j i) (j i') (j i''))
  simp only [Units.val_mul, rsT_mul] at co
  have e : ∀ {T T' : Z.Opens} (h : T' ≤ T) (u : Γ(Z, T)ˣ), (res h u).val = resG Z h u.val := fun _ _ => rfl
  have r : ∀ {T T' : Z.Opens} (h : T' ≤ T) (s : Γ(Z, T)), O ≤ T' → rsT (resG Z h s) O = rsT s O :=
    fun h s hO => by rw [← rsT_of_le h, rsT_rsT h hO]
  rw [e, e, e, r _ _ T3, r _ _ T3, r _ _ T3] at co
  set a := rsT (L.g (j i) (j i')).val O
  set b := rsT (L.g (j i') (j i'')).val O
  set a' := rsT (L.g (j i) (j i'))⁻¹.val O
  set b' := rsT (L.g (j i') (j i''))⁻¹.val O
  set e' := rsT (L.g (j i) (j i''))⁻¹.val O
  have ha : a * a' = 1 := rsT_unit (l₁.trans m₁) _
  have hb : b * b' = 1 := rsT_unit (l₂.trans m₂) _
  have he : rsT (L.g (j i) (j i'')).val O * e' = 1 := rsT_unit (l₃.trans m₃) _
  rw [← co] at he ⊢
  have hdm := hd.2.1 O le_top a b
  rw [hdm]
  linear_combination (-(d O a * a' + d O b * b')) * he + (d O a * b * e') * ha + (d O b * a * e') * hb

theorem exists_dlog_add_coboundary_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (y : ∀ i, Γ(t.G.left, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (inf_le_left.trans (hW i)) (cc b) * (dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i')) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hdd J W j hW hWc hj z hz
  let K := {p : t.G.left.affineOpens × J // p.1.1 ≤ W p.2}
  let V : K → t.G.left.Opens := fun p => p.1.1.1
  let σ : K → J := fun p => p.1.2
  have hVσ : ∀ p, V p ≤ W (σ p) := fun p => p.2
  have hVt : ∀ i, W i ≤ ⨆ p, V p := by
    intro i x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := t.G.left.isBasis_affineOpens.exists_subset_of_mem_open hx (W i).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, i), hUW⟩, hxU⟩
  have cover : ⨆ p, V p = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 := by
    refine le_antisymm (iSup_le fun p => (hVσ p).trans (hW _)) ?_
    rw [← hWc]
    exact iSup_le hVt
  let z' : C1 V := fun p p' => rsT (z (σ p) (σ p')) (V p ⊓ V p')
  have hz' : IsCoc V z' := by
    intro p p' p''
    have h := congrArg (fun s => rsT s (V p ⊓ V p' ⊓ V p'')) (hz (σ p) (σ p') (σ p''))
    simp only [rsT_add] at h
    have l₁ : V p ⊓ V p' ⊓ V p'' ≤ W (σ p) ⊓ W (σ p') ⊓ W (σ p'') :=
      inf_le_inf (inf_le_inf (hVσ p) (hVσ p')) (hVσ p'')
    simp only [z']
    rw [rsT_rsT (inf_le_inf (hVσ p) (hVσ p')) inf_le_left, rsT_rsT (inf_le_inf (hVσ p') (hVσ p''))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_rsT (inf_le_inf (hVσ p) (hVσ p'')) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
    rwa [rsT_rsT inf_le_left l₁, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) l₁,
      rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) l₁] at h
  obtain ⟨cc, y', hy'⟩ := _root_.GlobalTheory.CechAff.exists_dlog_add_coboundary_affine E H R t P m tt htt hab c hc n v' dd' hdd K V (fun p => j (σ p))
    (fun p => (hVσ p).trans (hW _)) cover (fun p => (hVσ p).trans (hj _)) (fun p => p.1.1.2) z' hz'
  let dl : Fin n → C1 W := fun b i i' => dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) *
    rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')
  have hdl : ∀ b, IsCoc W (dl b) := fun b => isCoc_dlg t.PP.L t.PP.isLB (hdd b).1 W j hj
  let c0 : C1 W := fun i i' => z i i' - ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1
    (inf_le_left.trans (hW i)) (cc b) * dl b i i'
  let Cf : ∀ O : t.G.left.Opens, O ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → Fin n → Γ(t.G.left, O) :=
    fun O h b => (t.G.hom.appLE _ O h).hom (cc b)
  have key : ∀ (a a' : J) {O : t.G.left.Opens} (l : O ≤ W a ⊓ W a'),
      rsT (c0 a a') O = rsT (z a a') O - ∑ b, Cf O (l.trans (inf_le_left.trans (hW a))) b * rsT (dl b a a') O := by
    intro a a' O l
    simp only [c0]
    rw [rsT_sub, rsT_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [rsT_mul, rsT_appLE _ _ _ l]
  have hc0 : IsCoc W c0 := by
    intro i i' i''
    have l₁ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i' := inf_le_left
    have l₂ : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have l₃ : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have h0 := hz i i' i''
    rw [key i i' l₁, key i' i'' l₂, key i i'' l₃]
    have hs : ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i') (W i ⊓ W i' ⊓ W i'') +
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i' i'') (W i ⊓ W i' ⊓ W i'') =
        ∑ b, Cf _ (l₁.trans (inf_le_left.trans (hW i))) b * rsT (dl b i i'') (W i ⊓ W i' ⊓ W i'') := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, hdl b i i' i'']
    linear_combination h0 - hs
  have hB : ∀ p p', rsT (c0 (σ p) (σ p')) (V p ⊓ V p') = rsT (y' p') (V p ⊓ V p') - rsT (y' p) (V p ⊓ V p') := by
    intro p p'
    have l : V p ⊓ V p' ≤ W (σ p) ⊓ W (σ p') := inf_le_inf (hVσ p) (hVσ p')
    rw [key _ _ l, show rsT (z (σ p) (σ p')) (V p ⊓ V p') = z' p p' from rfl, hy' p p']
    have hs : ∀ b, rsT (dl b (σ p) (σ p')) (V p ⊓ V p') =
        dd' b (V p ⊓ V p') (rsT (t.PP.L.g (j (σ p)) (j (σ p'))).val (V p ⊓ V p')) *
          rsT (t.PP.L.g (j (σ p)) (j (σ p')))⁻¹.val (V p ⊓ V p') := fun b => by
      simp only [dl]
      rw [rsT_mul, rsT_field (hdd b).1 l, rsT_rsT (inf_le_inf (hj _) (hj _)) l, rsT_rsT (inf_le_inf (hj _) (hj _)) l]
    simp only [hs]
    ring
  obtain ⟨y, hy⟩ := isCob_of_refine_le W c0 hc0 V σ hVσ hVt y' hB
  refine ⟨cc, y, fun i i' => ?_⟩
  have := hy i i'
  simp only [c0] at this
  linear_combination this

end GlobalTheory.CechH1Local
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteKernelNearDiagonalAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem evc_symm {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    {Y : Over S} (a b : Y ⟶ G) : evc hP a b = evc hP b a := by
  have e := congrArg (CechPic.pull (lift b a).left) ((cls_eq_iff hP (pull_isLB hP _)).2 hs)
  rw [cls_pull hP _ (pull_isLB hP _), ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd] at e
  exact e.symm

theorem evc_eq_zero_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) {Y : Over S} (t : Y ⟶ T) (w : Y ⟶ G) :
    evc hP (t ≫ x) w = 0 := by
  have e := congrArg (CechPic.pull (lift w t).left) ((triv_ev_iff hP _ _).1 hx)
  rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem memKL_of_triv {P : LB (G ⊗ G).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd G G) (fst G G)).left))
    (a₁ : IsAdditive P) (a₂ : IsAdditive (AbDual.swap P)) {T : Over S} {x : T ⟶ G}
    (hx : Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left)) :
    MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) x := by
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff G (P.pull (lift (𝟙 G) (𝟙 G)).left) x).IsLB := LB.isLB_linComb hL _ _
  have hdiag : ∀ {Y : Over S} (y : Y ⟶ G), CechPic.pull y.left (cls _ hL) = evc hP y y := fun y => by
    rw [cls_pull hP _ hL, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have z : cls _ hD = 0 := by
    have e₁ := pull_translDiff hL x hD (fst T G) (snd T G)
    rw [lift_fst_snd, Over.id_left, pull_id, hdiag, hdiag] at e₁
    rw [e₁, (isAdditive_iff hP).1 a₁, (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂,
      (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂, evc_eq_zero_of_triv hP hx, evc_eq_zero_of_triv hP hx,
      evc_symm hP hs (snd T G) (fst T G ≫ x), evc_eq_zero_of_triv hP hx]
    simp
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, z, map_zero]

end GlobalTheory.KernelNear

namespace GlobalTheory.KernelNear

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem exists_finite_kernel_near : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → ∀ s ∈ W, ∃ (V₀ : S'.Opens) (Z : Over S') (i : Z ⟶ G), s ∈ V₀ ∧ Mono i ∧ IsFinite (Z.hom ∣_ V₀) ∧ (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) ∧ (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) ∧ (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) ∧ (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V₀ : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → ∃ z : T ⟶ Z, z ≫ i = x) ∧ (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧ ∃ c : (P.pull (lift (snd G (Over.mk (U.ι ≫ T.hom)) ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ z ≫ i) (fst G (Over.mk (U.ι ≫ T.hom)))).left).Gen, c.IsGen) := by
  intro S' _ G _ _ P hG hP h₁ h₂ hs W hW s hsW
  obtain ⟨V₀, hV₀, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := W) hsW
  obtain ⟨D, _, Q, h, hDab, q, -, hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom S' G G (𝟙 G) P hG hG inferInstance hP h₁ h₂
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have hD : ∀ {Y : Over S'} (a b : Y ⟶ G), evc hP a b = evc q.isLB a (b ≫ h) := fun a b => by
    have e' := (cls_eq_iff (pull_isLB hP _) (pull_isLB q.isLB _)).2 e
    rw [MonoidalCategory.id_tensorHom_id, Over.id_left, cls_pull hP _ (pull_isLB hP _), pull_id,
      cls_pull q.isLB _ (pull_isLB q.isLB _)] at e'
    rw [evc, e', ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd]
    rfl
  have K : ∀ {T : Over S'} (x : T ⟶ G), Triv (P.pull (lift (snd G T ≫ x) (fst G T)).left) ↔ x ≫ h = 1 := by
    intro T x
    rw [triv_ev_iff hP, evc_symm hP hs, hD, Category.assoc]
    refine ⟨fun hx => q.eq_one _ ((triv_ev_iff q.isLB _ _).2 hx), fun hx => ?_⟩
    rw [hx, MonObj.comp_one]
    exact evc_one_right q.isLB q.zero _
  have : Mono (η[D]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
  have kerh : ∀ {T : Over S'} (z : T ⟶ pullback h (η[D])), (z ≫ pullback.fst h (η[D])) ≫ h = 1 := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, toUnit_unique (z ≫ pullback.snd _ _) (toUnit _)]
    rfl
  have fac : ∀ {T : Over S'} (x : T ⟶ G), x ≫ h = 1 → ∃ z : T ⟶ pullback h (η[D]), z ≫ pullback.fst h (η[D]) = x :=
    fun x hx => ⟨pullback.lift x (toUnit _) (by rw [hx]; rfl), pullback.lift_fst _ _ _⟩
  have hcl : IsClosedImmersion (pullback.fst h (η[D])).left := by
    have hpb := (IsPullback.of_hasPullback h (η[D])).map (Over.forget S')
    have := hDab.proper
    have : IsClosedImmersion ((η[D]).left ≫ D.hom) := by
      rw [Over.w (η[D])]
      exact (inferInstance : IsClosedImmersion (𝟙 S'))
    have : IsClosedImmersion (η[D]).left := IsClosedImmersion.of_comp _ D.hom
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip this
  refine ⟨V₀, pullback h (η[D]), pullback.fst h (η[D]), hsV, inferInstance,
    GlobalTheory.T.relatively_ample_closed_immersion S' G P hG hP V₀ hV₀ (hW V₀ fun _ hx => hVW hx) _ _ hcl
      (fun T z _ => memKL_of_triv hP hs a₁ a₂ ((K _).2 (kerh z))), ?_, ?_, ?_, ?_, ?_⟩
  · intro T _
    exact fac 1 (MonObj.one_comp h)
  · intro T a b _
    refine fac _ ?_
    rw [MonObj.mul_comp, kerh, kerh, _root_.mul_one]
  · intro T a _
    refine fac _ ?_
    rw [GrpObj.inv_comp, kerh, inv_one]
  · intro T x _ hx
    exact fac x ((K x).1 hx)
  · intro T z _ p
    refine ⟨⊤, trivial, (K _).2 ?_⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc z, kerh, MonObj.comp_one]

end GlobalTheory.KernelNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.DescentPow

theorem exists_cTrait_norm_eqAt {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z} (hi : IsOpenImmersion i)
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (φ : InvFun ℤ) (ι : ℕ) (D : EffCartierData Y.Z)
    (hord : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a})
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hy : Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i)
    (z₁ : X₁.M.Z) (hz : πY (y (cPt p)) = z₁) :
    ∃ c : CTrait X₁ p z₁, c.y = y ≫ πY ∧ ∀ f, EqAt Y D (y (cPt p)) f →
      ‖Y.val (gPt p ≫ y) f‖ = Real.exp (-(c.sc * (ι * φ.evalZ c.T.β))) := by
  obtain ⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩ := _root_.GlobalTheory.Poinc.exists_trait_of_classical_point g n F Z i hi W8 X₁ Y πY p y hy
  have hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext v
    exact hj v
  refine ⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩
  · rw [Scheme.Hom.comp_apply]; exact hz
  · rw [← Category.assoc, ← Category.assoc, hgen]
    simp only [Category.assoc]
    rw [hT]
  · obtain ⟨a, ha, hI⟩ := hord T ξ hT
    have hc : ξ (closedPoint T.V) = y (cPt p) := by
      rw [← hξ, Scheme.Hom.comp_apply]
      exact congrArg ξ (IsLocalRing.comap_closedPoint j).symm
    rw [← hc] at hf
    have key := _root_.GlobalTheory.Poinc.EqNormAt.norm_val_eqAt _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf
    rw [hξ] at key
    have hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ := by
      refine norm_pos_iff.2 ?_
      rw [map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact T.irr.ne_zero
    show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.β)))
    rw [key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

theorem val_comp_of_centre {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (hHom : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY) {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z) {z : X₁.M.Z}
    (hz : πY (y (cPt q)) = z) {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z) :
    Y.val (gPt q ≫ y) a = X₁.M.val (gPt q ≫ y ≫ πY) a := by
  have hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z :=
    hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous
  have := hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)
  rw [← Category.assoc]
  exact this.symm

theorem exists_idealSheaf_comap_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ (X₁ : Setup F W8 i) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → IsProjOver X₁.M.s → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι' * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W8 hE hθi X₁ ι Y πY D hι hP hHom hprop hnorm hsupp hord
  have hi : IsOpenImmersion i := hθ.2.2.1
  obtain ⟨d, hd, hA⟩ := _root_.GlobalTheory.Poinc.exists_approxAt g n F W8 Z i X₁ hE hθi hg φ hφ
  obtain ⟨k, hk⟩ : ι ∣ Nat.lcm ι d := Nat.dvd_lcm_left ι d
  obtain ⟨m, hm⟩ : d ∣ Nat.lcm ι d := Nat.dvd_lcm_right ι d
  have hL0 : 0 < Nat.lcm ι d := Nat.lcm_pos hι hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega
  have hAL : ApproxAt X₁ φ (Nat.lcm ι d) := hm ▸ _root_.GlobalTheory.Poinc.approxAt_mul g n F W8 Z i X₁ φ d m hm0 hA

  have hord' : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = (Nat.lcm ι d : ℕ) * φ.evalZ T.β ∧ idlAlong (D.nsmul k).idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
    intro T ξ h
    obtain ⟨a, ha, hI⟩ := hord T ξ h
    refine ⟨k * a, ?_, ?_⟩
    · rw [hk]; push_cast; rw [ha]; ring
    · rw [GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]
  have hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support := by
    intro y hy
    obtain ⟨j, hj⟩ := D.exists_mem y
    rw [(D.nsmul k).mem_support_iff j hj] at hy
    rw [D.mem_support_iff j hj]
    intro h
    apply hy
    change y ∈ Y.Z.basicOpen (D.f j ^ k)
    rw [Scheme.basicOpen_pow _ _ hk0]
    exact h

  let U : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ i.opensRange
  have hmemU : ∀ y : Y.Z, y ∈ U ↔ X₁.π (πY y) ∈ Set.range i := fun y => by
    show (πY ≫ X₁.π) y ∈ Set.range i ↔ _
    rw [Scheme.Hom.comp_apply]
  have hU : (U : Set Y.Z).Nonempty := by
    refine ⟨Y.pt (closedPoint X₁.Ω₁), (hmemU _).2 ?_⟩
    have e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u ≫ i := by
      rw [← Category.assoc, hHom, Category.assoc, X₁.comp]
    have e' := congrArg (fun h : Sp X₁.Ω₁ ⟶ Z => h (closedPoint X₁.Ω₁)) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact ⟨_, e'.symm⟩
  have hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U := fun x hx hxU => hsupp x (hsub x hx) ((hmemU x).1 hxU)
  have hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U →
      Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro q _ y hy _ ⟨w, rfl⟩
    have := (hmemU _).1 (hy ⟨w, rfl⟩)
    simpa only [← Category.assoc, Scheme.Hom.comp_apply] using this
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.Poinc.exists_idealSheaf_comap_eq_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by
    intro z₀ _ x hxz hx
    obtain ⟨p, hp, y₀, hcen⟩ := _root_.GlobalTheory.Poinc.exists_cen_main _ _ Y x hx U hU
    obtain ⟨c₀, hc₀y, hc₀⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀
      (by rw [hcen.1, hxz])
    refine ⟨p, hp, y₀, hcen, fun e => ?_⟩
    obtain ⟨f, hf0, hfall⟩ := hAL p z₀ c₀ e
    have hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀ := (X₁.M.stalkEquiv z₀ f).2
    refine ⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩
    · rw [hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0]
      show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖
      rw [hc₀y]
    · intro q hq y hyz hyU f' hf'
      have hpq : p = q := _root_.GlobalTheory.Poinc.eq_of_cPt_eq X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])
      subst hpq
      obtain ⟨c, hcy, hc⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz
      have hcv : ∀ a, c.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a) := fun a => by
        rw [val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]
        show X₁.M.val (gPt p ≫ c.y) _ = _
        rw [hcy]
      rcases hfall c with h1 | ⟨h, hh, h2⟩
      · left
        rw [← hcv, hc f' hf']
        exact h1
      · right
        refine ⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩
        · by_contra hne
          push_neg at hne
          apply (IsLocalRing.mem_maximalIdeal _).1 hh
          have hu : IsUnit (X₁.M.stalkEquiv z₀ h) :=
            (RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩
          exact (MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu
        · rw [← hcv, ← hcv]
          exact h2)
  refine ⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩
  · rw [hJ]
    intro y hy
    exact hsupp y (hsub y hy)
  · rw [hJ]
    exact hord'

end GlobalTheory.Poinc.DescentPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.CorrForm
open GlobalTheory.AbDual

theorem exists_isCorrForm_obj : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ := by
  intro p _ D R _ b N _ _ k _ _ t o₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  have C := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  exact exists_isCorrForm C o₀.isLB o₀.rig₁ o₀.rig₂

end GlobalTheory.UPel.HT.CorrForm
end
end

