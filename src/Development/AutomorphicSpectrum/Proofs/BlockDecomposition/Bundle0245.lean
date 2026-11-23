module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0234

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVectorBundle
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrVB
open GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem rp_class {W : X.Opens} {P : ObjectProperty (Thick (LL q))} {d r : ℕ} {u : Fin d → ∀ T : Thick (LL q), T.B}
    {x : Idx r d → Γ(X, W)} {c c' : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x c') : c = c' := by
  obtain ⟨f, hf, rfl, hs⟩ := h
  obtain ⟨f', hf', rfl, hs'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hs s).trans (hs' s).symm)
  subst e
  rfl

theorem inU_mono {W W' : X.Opens} (h : W' ≤ W) {T : Thick (LL q)} (hT : InU W' T) : InU W T :=
  hT.trans (fun _ hx => h hx)

theorem isLift_res {V W : X.Opens} (h : W ≤ V) {d : ℕ} {t : Fin d → Γ(X, V)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift V t u) {t' : Fin d → Γ(X, W)} (ht : ∀ i, t' i = rs h (t i)) : IsLift W t' u := by
  intro i T hT
  rw [ht, hu i T (inU_mono h hT), ev_res h T (inU_mono h hT) hT]

theorem st_iff {Q : ObjectProperty (Thick (LL q))} {W : X.Opens} (T : Thick (LL q)) :
    St Q {W} T ↔ Q T ∧ InU W T := by
  constructor
  · rintro ⟨h, V, hV, hi⟩
    obtain rfl : V = W := hV
    exact ⟨h, hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨h, W, rfl, hi⟩

theorem inU_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have e : capO U i = ⨅ a ∈ (Finset.univ : Finset (Fin n)), U (i a) := by simp [capO]
  rw [e, _root_.GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun a => U (i a)) Finset.univ T]
  simp

theorem capT_eq (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => SS q l s (U α)) i = SS q l s (capO U i) := by
  funext T
  refine propext ⟨fun h => ?_, fun h a => ?_⟩
  · exact (st_iff T).2 ⟨((st_iff T).1 (h 0)).1, (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2⟩
  · obtain ⟨h1, h2⟩ := (st_iff T).1 h
    exact (st_iff T).2 ⟨h1, (inU_capO U i T).1 h2 a⟩

def Free (W : X.Opens) (P : ObjectProperty (Thick (LL q))) (r : ℕ) {d : ℕ} (u : Fin d → ∀ T : Thick (LL q), T.B) : Prop :=
  (∀ cl : HU (GF q r) P r, ∃ x, Rp (W := W) P u x cl) ∧ ∀ x : Idx r d → Γ(X, W), Rp (W := W) P u x 0 → x = 0

section Forms
variable {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
  {P : ObjectProperty (Thick (LL q))} {r : ℕ}

theorem rp_zero (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) :
    Rp (W := W) P u (0 : Idx r d → Γ(X, W)) (0 : HU (GF q r) P r) := by
  obtain ⟨c, hc⟩ := hE W t u hu P hP r 0
  have h2 := (hA W t u hu P hP r _ _ _ _ hc (hA W t u hu P hP r _ _ _ _ hc hc).2).1
  rw [add_neg_cancel, add_neg_cancel] at h2
  exact h2

theorem rp_sum (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) {κ' : Type} (S : Finset κ')
    (x : κ' → Idx r d → Γ(X, W)) (c : κ' → HU (GF q r) P r) (h : ∀ k ∈ S, Rp (W := W) P u (x k) (c k)) :
    Rp (W := W) P u (∑ k ∈ S, x k) (∑ k ∈ S, c k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact rp_zero hE hA hu hP
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hA W t u hu P hP r _ _ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).1

theorem rp_coef (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u)
    {x x' : Idx r d → Γ(X, W)} {c : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x' c) : x = x' := by
  have h2 := (hA W t u hu P hP r _ _ _ _ h (hA W t u hu P hP r _ _ _ _ h' h').2).1
  rw [add_neg_cancel c] at h2
  exact add_neg_eq_zero.1 (hF.2 _ h2)

theorem exists_equiv (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u) :
    ∃ e : HU (GF q r) P r ≃+ (Idx r d → Γ(X, W)), ∀ cl, Rp (W := W) P u (e cl) cl := by
  choose f hf using hF.1
  choose g hg using fun x => hE W t u hu P hP r x
  exact ⟨{ toFun := f, invFun := g, left_inv := fun c => rp_class (hg _) (hf c),
           right_inv := fun x => rp_coef hA hu hP hF (hf _) (hg x),
           map_add' := fun a b => rp_coef hA hu hP hF (hf _) (hA W t u hu P hP r _ _ _ _ (hf a) (hf b)).1 }, hf⟩

end Forms

theorem free_at (hL : StLoc) {l s : ℕ} (hb : TFBase (dividedPowersBot O) l s) {V W : X.Opens} (h : W ≤ V)
    (hW : IsAffineOpen W) {d : ℕ} (c : Coord q V d) {u : Fin d → ∀ T : Thick (LL q), T.B} (hu : IsLift V c.t u)
    {r : ℕ} (hr : r < s) {P : ObjectProperty (Thick (LL q))} (hP : P = SS q l s W) : Free W P r u := by
  subst hP
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.CompanionTheory.CoordRes.main c h hW
  exact hL l s hb q c' u (isLift_res h hu hc') r hr

theorem chg (hE : StExists) (hA : StAdd) (hR : StRes) (hAct : StAct) {W W₂ : X.Opens} (h : W ≤ W₂) {da db : ℕ}
    {ta : Fin da → Γ(X, W₂)} {tb : Fin db → Γ(X, W₂)} {ua : Fin da → ∀ T : Thick (LL q), T.B}
    {ub : Fin db → ∀ T : Thick (LL q), T.B} (hua : IsLift W₂ ta ua) (hub : IsLift W₂ tb ub)
    {P P₂ : ObjectProperty (Thick (LL q))} (hPP : P ≤ P₂) (hP : ∀ T, P T → InU W T) (hP₂ : ∀ T, P₂ T → InU W₂ T) {r : ℕ}
    (A : HU (GF q r) P₂ r ≃+ (Idx r da → Γ(X, W₂))) (hA' : ∀ cl, Rp (W := W₂) P₂ ua (A cl) cl)
    (B : HU (GF q r) P₂ r ≃+ (Idx r db → Γ(X, W₂))) (hB' : ∀ cl, Rp (W := W₂) P₂ ub (B cl) cl)
    [DecidableEq (Idx r db)] (x : HU (GF q r) P r) (y : Idx r db → Γ(X, W)) (hy : Rp (W := W) P ub y x) :
    Rp (W := W) P ua (fun k => ∑ k', rs h (A (B.symm (Pi.single k' 1)) k) * y k') x := by
  have hua' : IsLift W (fun i => rs h (ta i)) ua := isLift_res h hua fun _ => rfl
  have hub' : IsLift W (fun i => rs h (tb i)) ub := isLift_res h hub fun _ => rfl
  have hb1 : ∀ k', Rp (W := W₂) P₂ ub (Pi.single k' 1) (B.symm (Pi.single k' 1)) := fun k' => by
    have := hB' (B.symm (Pi.single k' 1))
    rwa [AddEquiv.apply_symm_apply] at this
  choose m hm using fun k' => hAct W P hP r (y k')
  have hd1 : ∀ k', Rp (W := W) P ub (fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hub' _ _ (hR W₂ W h tb ub hub P₂ P hPP hP₂ hP r _ _ (hb1 k'))
  have hd2 : ∀ k', Rp (W := W) P ua (fun I => y k' * rs h (A (B.symm (Pi.single k' 1)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hua' _ _ (hR W₂ W h ta ua hua P₂ P hPP hP₂ hP r _ _ (hA' _))
  have s1 := rp_sum hE hA hub' hP Finset.univ _ _ fun k' _ => hd1 k'
  have s2 := rp_sum hE hA hua' hP Finset.univ _ _ fun k' _ => hd2 k'
  have e1 : (∑ k', fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I)) = y := by
    funext I
    rw [Finset.sum_apply, Finset.sum_eq_single I]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · simp
  rw [e1] at s1
  rw [rp_class s1 hy] at s2
  convert s2 using 1
  funext k
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem capO_pair {ι : Type} (U : ι → X.Opens) (α β : ι) : capO U ![α, β] = U α ⊓ U β := by
  refine le_antisymm (le_inf (capO_le U _ 0) (capO_le U _ 1)) (le_iInf fun a => ?_)
  fin_cases a
  · exact inf_le_left
  · exact inf_le_right

theorem capT_inU (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q))
    (h : capT (fun α => SS q l s (U α)) i T) : InU (capO U i) T :=
  (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2

theorem ss_inU (l s : ℕ) (W : X.Opens) (T : Thick (LL q)) (h : SS q l s W T) : InU W T := ((st_iff T).1 h).2

section Main
variable {ι : Type} (U : ι → X.Opens) (d : ι → ℕ) (c : ∀ α, Coord q (U α) (d α))

def uu (α : ι) : Fin (d α) → ∀ T : Thick (LL q), T.B := fun k T => lft (U α) T ((c α).t k)

theorem uu_lift (α : ι) : IsLift (U α) (c α).t (uu U d c α) := fun k T h => lft_spec T h _

theorem uu_res (α : ι) {W : X.Opens} (h : W ≤ U α) : IsLift W (fun k => rs h ((c α).t k)) (uu U d c α) :=
  isLift_res h (uu_lift U d c α) fun _ => rfl

end Main

theorem main : StExists → StAdd → StSmul → StRes → StAct → StLoc → StVB := by
  classical
  intro hE hA hS hR hAct hL O _ l s hb X q ι _ U d c ha r hr
  have hPi : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (T : Thick (LL q)), capT (fun α => SS q l s (U α)) i T → InU (capO U i) T :=
    fun i T h => capT_inU l s U i T h
  have hFi : ∀ (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι),
      Free (capO U i) (capT (fun α => SS q l s (U α)) i) r (uu U d c (i a)) := fun n a i =>
    free_at hL hb (capO_le U i a) (ha n i) (c (i a)) (uu_lift U d c (i a)) hr (capT_eq l s U i)
  choose E hEr using fun (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι) =>
    exists_equiv hE hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i)
  have aff2 : ∀ α β, IsAffineOpen (U α ⊓ U β) := fun α β => by
    rw [← capO_pair]
    exact ha 1 _
  choose A hAr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c α inf_le_left)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_left (aff2 α β) (c α) (uu_lift U d c α) hr rfl)
  choose B hBr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c β inf_le_right)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_right (aff2 α β) (c β) (uu_lift U d c β) hr rfl)
  refine ⟨{ κ := fun α => Idx r (d α)
            fin := fun _ => inferInstance
            g := fun α β k k' => A α β ((B α β).symm (Pi.single k' 1)) k
            e := fun n a => AddEquiv.piCongrRight fun i => E n a i
            e_smul := ?_
            e_δ := ?_
            e_chg := ?_ }⟩
  · intro n a z x i k
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (z • x i))
      (hS _ _ _ (uu_res U d c (i a) (capO_le U i a)) _ (hPi i) r _ _ z (hEr n a i (x i)))
    exact congrFun this k
  · intro n a b x i k
    have := rp_coef hA (uu_res U d c (i (b.succAbove a)) (capO_le U i (b.succAbove a))) (hPi i) (hFi (n + 1) (b.succAbove a) i)
      (hEr (n + 1) (b.succAbove a) i _)
      (hR _ _ (capO_comp U i b.succAbove) _ _ (uu_res U d c (i (b.succAbove a)) (capO_le U (i ∘ b.succAbove) a))
        _ (capT (fun α => SS q l s (U α)) i) (fun _ h _ => h _) (hPi _) (hPi i) r _ _ (hEr n a (i ∘ b.succAbove) (x (i ∘ b.succAbove))))
    exact congrFun this k
  · intro n a b x i k
    have hle : capO U i ≤ U (i a) ⊓ U (i b) := le_inf (capO_le U i a) (capO_le U i b)
    have hPP : capT (fun α => SS q l s (U α)) i ≤ SS q l s (U (i a) ⊓ U (i b)) := fun T h =>
      (st_iff T).2 ⟨((st_iff T).1 (h a)).1, inU_mono hle (hPi i T h)⟩
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (x i))
      (chg hE hA hR hAct hle (uu_res U d c (i a) inf_le_left) (uu_res U d c (i b) inf_le_right) hPP (hPi i)
        (ss_inU l s _) (A (i a) (i b)) (hAr _ _) (B (i a) (i b)) (hBr _ _) (x i) _ (hEr n b i (x i)))
    exact congrFun this k

end GlobalTheory.CompanionTheory.GrVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSheafWellFoundedGt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem idealSheafData_wellFoundedGT :
    ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  intro X _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U.1 : X.Opens) : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, (U.1 : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  have hcov : ⨆ i : t, ((i.1 : X.affineOpens).1 : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨U, hUt, hxU⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩
  have hnoeth : ∀ i : t, WellFoundedGT (Ideal Γ(X, (i.1 : X.affineOpens).1)) := fun i => by
    have : IsNoetherianRing Γ(X, (i.1 : X.affineOpens).1) :=
      IsLocallyNoetherian.component_noetherian i.1
    infer_instance
  let φ : X.IdealSheafData → (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) :=
    fun I i => I.ideal i.1
  have hφ : StrictMono φ := by
    refine Monotone.strictMono_of_injective (fun I J h i => h i.1) ?_
    intro I J h
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : t => i.1) hcov
      (fun i => congrFun h i)
  have h1 : WellFoundedLT (∀ i : t, (Ideal Γ(X, (i.1 : X.affineOpens).1))ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) := h1
  exact hφ.wellFoundedGT

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IncPtInjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ElOnto

variable {l : ℕ} [Fact l.Prime]

theorem elMap_full {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (hu : ∀ A, Function.Injective (u.app A)) : (elMap u).Full := by
  refine ⟨fun {X Y} f => ⟨⟨f.1, ?_⟩, rfl⟩⟩
  apply hu
  exact (NatTrans.naturality_apply u ((testι l).map f.1) X.2).trans f.2

theorem elMap_faithful {P P' : PAlg l ⥤ Type} (u : P ⟶ P') : (elMap u).Faithful := by
  refine ⟨fun {X Y} f g h => Functor.Elements.Hom.ext ?_⟩
  have h' := congrArg (fun f => f.hom) h
  exact h'

variable {O : Type} [CommRing O]

theorem inc_pt_injective {F : Fn O} (κ : O →+* OC l) (V : F.Sub) (A : PAlg l) :
    Function.Injective ((V.inc.pt κ).app A) := by
  intro a b h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  exact h'

theorem onto_subEl : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 S k n hn
  refine ⟨elMap_full _ (inc_pt_injective κ _), elMap_faithful _, ?_, ?_⟩
  · intro T α hα
    exact (𝒜.V α).in_map _ (T.2.1.2 α hα)
  · intro T hT
    obtain ⟨hs, hj⟩ := (_root_.GlobalTheory.CompanionTheory.AcrMod.acr_modp T.1.obj n).2.2.2.2.2.2 k hn
    refine ⟨⟨⟨⟨T.2.1, fun α hα => 𝒜.jac α _ _ (CommRingCat.ofHom (uJ k T.1.obj n)) T.2.1 hs hj (hT α hα)⟩, T.2.2⟩⟩, ⟨Iso.refl _⟩⟩

end GlobalTheory.CompanionTheory.ElOnto
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFirstChernThickeningMuBOfIsFirstChernDeRham
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernRationalLift

variable {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ)

abbrev famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) : C ⥤ Thick (smFun X q) :=
  G ⋙ (smO γ q 1 s {⊤}).G ⋙ (TO q 1 s {⊤}).ι

theorem pt_famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) (c : C) :
    pt ((famK γ q s G).obj c) = pt (G.obj c).obj := Category.comp_id _

def liftK {C : Type 1} [Category.{0} C] {G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory} {D : E.LineData X}
    (Λ : B.CLift (q := q) (b := nlBase B' I γ 0) (ht := rfl) (κ := κA K I) (G ⋙ (TS γ q 1 s {⊤}).ι) D) :
    CLiftK (famK γ q s G) D where
  p c := Λ.p c
  hp c := (Λ.hp c).trans (Category.comp_id _).symm
  w φ := Λ.w φ
  hw φ h := Λ.hw φ h

theorem isFirstChernThickening_muB_of_isFirstChernDeRham (D : E.LineData X) (c : HdR q 2)
    (h : IsFirstChernDeRham (q := q) D c) :
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := by
  intro C _ G hG Λ
  have hpd : ∀ c', ((famK γ q s G).obj c').pdPow s = ⊥ := fun c' => ((smO γ q 1 s {⊤}).G.obj (G.obj c')).property.1.1
  have hV : ∀ c', ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((famK γ q s G).obj c') := by
    intro c'
    obtain ⟨V, ⟨σ, hσ⟩, hU⟩ := hG c'
    refine ⟨V, σ, hσ, ?_⟩
    unfold InU
    rw [pt_famK]
    exact hU
  obtain ⟨z, hz, hzv, hcls⟩ := h s C (famK γ q s G) hpd hV (liftK γ q s Λ)
  let m' : CH.Mor (famK γ q s G ⋙ O (smFun X q)) (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) (algebraMap K B') :=
    ⟨𝟭 _, fun T => (smO γ q 1 s {⊤}).o.τ (G.obj T), fun φ x => (smO γ q 1 s {⊤}).o.nat (G.map φ) x⟩
  have e : (show CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 from Λ.coc (RingHom.id _) s) = m'.pullC 2 z := by
    funext σ
    exact (hzv σ).symm
  have hb : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (m'.pullC 2 z) = 0 := by
    rw [m'.d_pullC, hz, map_zero]
  have hz' : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (Λ.coc (RingHom.id _) s) = 0 := (congrArg (CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) e).trans hb
  refine ⟨hz', ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 z hz hb
  have e2 : (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2 (muB γ q 1 s {⊤} 2 c) =
      m'.pull 2 ((CH.Mor.restrict (O (smFun X q)) (famK γ q s G)).pull 2 c) := by
    have a1 := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι) (smO γ q 1 s {⊤}).o 2 c).1
    have a2 := (CrystallineSemistableComparison.P.pull_comp ((CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι).comp (smO γ q 1 s {⊤}).o)
      (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G) 2 c).1
    have b := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (famK γ q s G)) m' 2 c).1
    exact (congrArg ((CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2) a1.symm).trans (a2.symm.trans b)
  rw [e2, ← hcls]
  refine Eq.trans ?_ e1.symm
  have key : ∀ (a : CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) (ha : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 a = 0),
      a = m'.pullC 2 z → (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls a ha =
        (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls (m'.pullC 2 z) hb := by
    rintro _ _ rfl
    rfl
  exact key _ hz' e

end GlobalTheory.CompanionTheory.FirstChernRationalLift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateLimitCongruence
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.QLim

theorem map_mem {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) (q : ℕ) {x : B}
    (hx : x ∈ S) : ϖ * x + x ^ q ∈ S :=
  S.add_mem (S.mul_mem hϖ hx) (S.pow_mem hx q)

theorem step_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) {a b c : B} (hb : b ∈ S) (hc : c ∈ S) {m : ℕ} (hm : 1 ≤ m)
    (hab : a - b = ϖ ^ m * c) :
    ∃ c' ∈ S, (ϖ * a + a ^ q) - (ϖ * b + b ^ q) = ϖ ^ (m + 1) * c' := by
  obtain ⟨s, hs, hqs⟩ := hq
  have hy : ϖ ^ m * c ∈ S := S.mul_mem (S.pow_mem hϖ m) hc
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Polynomial.X ^ q : Polynomial S)
    (⟨b, hb⟩ : S) (⟨ϖ ^ m * c, hy⟩ : S)
  have hk' : (b + ϖ ^ m * c) ^ q =
      b ^ q + (q : B) * b ^ (q - 1) * (ϖ ^ m * c) + (k : B) * (ϖ ^ m * c) ^ 2 := by
    have h := congrArg (Subtype.val) hk
    simpa [Polynomial.derivative_X_pow] using h
  have ha : a = b + ϖ ^ m * c := by linear_combination hab
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨c + s * b ^ (q - 1) * c + (k : B) * ϖ ^ m' * c ^ 2, ?_, ?_⟩
  · exact S.add_mem (S.add_mem hc (S.mul_mem (S.mul_mem hs (S.pow_mem hb _)) hc))
      (S.mul_mem (S.mul_mem k.2 (S.pow_mem hϖ _)) (S.pow_mem hc _))
  · rw [ha, hk', hqs]; ring

theorem iter_congr {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) {q : ℕ}
    (hq : ∃ s ∈ S, (q : B) = ϖ * s) (n : ℕ) :
    ∀ {a b c : B} {m : ℕ}, a ∈ S → b ∈ S → c ∈ S → 1 ≤ m → a - b = ϖ ^ m * c →
      ∃ c' ∈ S, ltIter ϖ q n a - ltIter ϖ q n b = ϖ ^ (m + n) * c' := by
  induction n with
  | zero =>
    intro a b c m _ _ hc _ hab
    exact ⟨c, hc, by simpa [ltIter] using hab⟩
  | succ n ih =>
    intro a b c m ha hb hc hm hab
    obtain ⟨c₁, hc₁, h₁⟩ := step_congr hϖ hq hb hc hm hab
    obtain ⟨c₂, hc₂, h₂⟩ := ih (map_mem hϖ q ha) (map_mem hϖ q hb) hc₁ (by omega) h₁
    refine ⟨c₂, hc₂, ?_⟩
    have e : m + (n + 1) = m + 1 + n := by omega
    rw [e]
    exact h₂

theorem exists_limit : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → (∀ n, v (n + 1) ^ q = v n) →
      ∃ Q ∈ S, ∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a := by
  intro B _ S F ϖ E q _ hq v hv hvq
  have hd : ∀ n, ∃ e ∈ S, ltIter ϖ q (n + 1) (v (n + 1)) - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * e := by
    intro n
    have h1 : (ϖ * v (n + 1) + v (n + 1) ^ q) - v n = ϖ ^ 1 * v (n + 1) := by
      rw [hvq]; ring
    obtain ⟨c, hc, h⟩ := iter_congr E.mem hq n (map_mem E.mem q (hv (n + 1))) (hv n) (hv (n + 1))
      le_rfl h1
    refine ⟨c, hc, ?_⟩
    have e : ltIter ϖ q (n + 1) (v (n + 1)) = ltIter ϖ q n (ϖ * v (n + 1) + v (n + 1) ^ q) := rfl
    rw [e, h, add_comm n 1]
  choose e he hde using hd
  let s : ℕ → B := fun n => Nat.casesOn n (v 0) e
  have hs : ∀ n, s n ∈ S := by
    intro n
    cases n with
    | zero => exact hv 0
    | succ n => exact he n
  obtain ⟨r, hr, hsum⟩ := E.sumS s hs
  have tel : ∀ N, ∑ n ∈ Finset.range (N + 1), ϖ ^ n * s n = ltIter ϖ q N (v N) := by
    intro N
    induction N with
    | zero => simp [s, ltIter]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hN : s (N + 1) = e N := rfl
      rw [hN, ← hde N]
      ring
  refine ⟨r, hr, fun n => ?_⟩
  obtain ⟨a, ha, h⟩ := hsum (n + 1)
  rw [tel n] at h
  exact ⟨a, ha, h⟩

end GlobalTheory.CompanionTheory.LTPer.QLim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedKillsToSome
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedFil

theorem red_kills_toSome : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r j : ℕ), ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSome (TS γ q l s 𝒱) r ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s 𝒱 c lam hc r j x hx
  exact GlobalTheory.CompanionTheory.RedFil.red_kills d q s 𝒱 c lam hc r j x hx

end GlobalTheory.CompanionTheory.RedFil
end

