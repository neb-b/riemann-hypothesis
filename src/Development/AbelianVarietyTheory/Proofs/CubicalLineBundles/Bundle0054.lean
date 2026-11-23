module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.PairingFibre

variable {S S' : Scheme.{0}} {s : S' ⟶ S}

theorem exists_hom {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hG : IsGrpPullback G' G s φ) (hH : IsGrpPullback H' H s ψ)
    (w : G ⟶ H) [IsMonHom w] : ∃ w' : G' ⟶ H', IsMonHom w' ∧ w'.left ≫ ψ = φ ≫ w.left := by
  let w' : G' ⟶ H' := Over.homMk (hH.1.lift (φ ≫ w.left) G'.hom (by rw [Category.assoc, Over.w, hG.1.w]))
    (hH.1.lift_snd _ _ _)
  have hw : w'.left ≫ ψ = φ ≫ w.left := hH.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G'), Geo.Tor.pushPt hH.1.w (x ≫ w') = Geo.Tor.pushPt hG.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have mul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ w' = (x ≫ w') * (y ≫ w') := by
    intro T x y
    apply SymBaseChange.pushPt_injective hH
    have a : Geo.Tor.pushPt hG.1.w (x * y) = Geo.Tor.pushPt hG.1.w x * Geo.Tor.pushPt hG.1.w y := map_mul (Geo.Tor.pushHom hG T) x y
    have b : Geo.Tor.pushPt hH.1.w ((x ≫ w') * (y ≫ w')) = Geo.Tor.pushPt hH.1.w (x ≫ w') * Geo.Tor.pushPt hH.1.w (y ≫ w') :=
      map_mul (Geo.Tor.pushHom hH T) _ _
    rw [pa, a, b, pa, pa, MonObj.mul_comp]
  refine ⟨w', ⟨?_, ?_⟩, hw⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S') ⟶ G') ≫ w' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem cube_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LBIso L' (L.pull φ)) {T : Over S} {T' : Over S'} (U : T'.left ⟶ T.left)
    (hU : U ≫ T.hom = T'.hom ≫ s) {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (hx : ∀ i, (x' i).left ≫ φ = U ≫ (x i).left) : LBIso (cubeLB G' x' L') ((cubeLB G x L).pull U) := by
  have hc : (cubeLB G x L).IsLB := DVR.linComb_isLB L hL _ _
  refine LBIso.trans (B := cubeLB G' x' (L.pull φ)) (DVR.linComb_isLB L' hL' _ _)
    (DVR.linComb_isLB _ (Geo.Tor.pull_isLB hL φ) _ _) (Geo.Tor.pull_isLB hc U) (PowPrimitive.lbIso_linComb w _ _) ?_
  exact LBIso.chartPull (Geo.Tor.chartPullLinComb L φ _ _ _ U fun I =>
    Geo.Tor.psum_push h x' x (Over.homMk U hU) (fun i => Over.OverMorphism.ext (hx i)) I.down)
    (Geo.Tor.chartPullPull _ U U rfl) (PolBaseChange.lbIso_refl hc)

theorem exists_gen_cube_one {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (T : Over S) :
    ∃ t : LB.Gen (cubeLB G (fun _ : Fin 2 => (1 : T ⟶ G)) L), t.IsGen := by
  refine (PrimNorm.hasGen_iff hL _ _).2 ?_
  have hp (I : Finset (Fin 2)) : psum G (fun _ : Fin 2 => (1 : T ⟶ G)) I = 1 := by
    unfold psum
    induction (List.finRange 2).filter (· ∈ I) with
    | nil => rfl
    | cons k l ih => exact (congrArg ((1 : T ⟶ G) * ·) ih).trans (_root_.mul_one _)
  simp_rw [hp]
  rw [show (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) =
    {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} by decide]
  classical
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp

theorem cube_zero {X Y G : Over S} [GrpObj X] [GrpObj Y] [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f₁ : X ⟶ G) (f₂ : Y ⟶ G) [IsMonHom f₁] [IsMonHom f₂] :
    LBIso (cubeLB G (fun _ : Fin 2 => (1 : 𝟙_ (Over S) ⟶ G)) L)
      ((cubeLB G ![fst X Y ≫ f₁, snd X Y ≫ f₂] L).pull (eSec (X ⊗ Y))) := by
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  refine cube_pull (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) hL hL
    (LBIso.chartPull (Geo.Tor.chartPullId L) (Geo.Tor.chartPullPull L _ (𝟙 _) rfl) (PolBaseChange.lbIso_refl hL)) _
    (by rw [eSec, Over.w, Category.comp_id]) _ _ fun i => ?_
  rw [eSec, ← Over.comp_left, ← Over.comp_left]
  congr 1
  fin_cases i <;> simp [Hom.one_def]

theorem weilEq_iff {X Y A B : Over S} {X' Y' A' B' : Over S'} [GrpObj X] [GrpObj Y] [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] [GrpObj X'] [GrpObj Y'] [GrpObj A'] [GrpObj B']
    {x : X'.left ⟶ X.left} {y : Y'.left ⟶ Y.left} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hX : IsGrpPullback X' X s x) (hY : IsGrpPullback Y' Y s y) (hA : IsGrpPullback A' A s a)
    (hB : IsGrpPullback B' B s b) {L : LB A.left} {M : LB B.left} {L' : LB A'.left} {M' : LB B'.left}
    (hL : L.IsLB) (hM : M.IsLB) (hL' : L'.IsLB) (hM' : M'.IsLB) (wL : LBIso L' (L.pull a)) (wM : LBIso M' (M.pull b))
    {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B} {f₁' : X' ⟶ A'} {f₂' : Y' ⟶ A'} {g₁' : X' ⟶ B'}
    {g₂' : Y' ⟶ B'} (e₁ : f₁'.left ≫ a = x ≫ f₁.left) (e₂ : f₂'.left ≫ a = y ≫ f₂.left)
    (e₃ : g₁'.left ≫ b = x ≫ g₁.left) (e₄ : g₂'.left ≫ b = y ≫ g₂.left) {k : Type} [Field k] (t : Sp k ⟶ S') :
    WeilEq L' f₁' f₂' M' g₁' g₂' t ↔ WeilEq L f₁ f₂ M g₁ g₂ (t ≫ s) := by
  have key : ∀ (n : ℕ) (p : Over.mk t ⟶ X') (q : Over.mk t ⟶ Y') (c : kˣ),
      ((Out.WeilIs A' L' n (p ≫ f₁') (q ≫ f₂') (unitOn c) ↔ Out.WeilIs B' M' n (p ≫ g₁') (q ≫ g₂') (unitOn c)) ↔
      (Out.WeilIs A L n (Geo.Tor.pushHom hX _ p ≫ f₁) (Geo.Tor.pushHom hY _ q ≫ f₂) (unitOn c) ↔
        Out.WeilIs B M n (Geo.Tor.pushHom hX _ p ≫ g₁) (Geo.Tor.pushHom hY _ q ≫ g₂) (unitOn c))) := by
    intro n p q c
    refine iff_congr (weilIs_grpPullback_of_comm S S' A A' s a L L' hL hL' hA wL _ _ _ _ _ _ _ ?_ ?_)
      (weilIs_grpPullback_of_comm S S' B B' s b M M' hM hM' hB wM _ _ _ _ _ _ _ ?_ ?_)
    all_goals
      show (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
      simp only [Category.assoc, e₁, e₂, e₃, e₄]
  have pw : ∀ {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ)
      (n : ℕ) (p : Over.mk t ⟶ G'), p ^ n = 1 ↔ Geo.Tor.pushHom h _ p ^ n = 1 := fun h n p => by
    rw [← map_pow]
    exact (map_eq_one_iff _ fun u v e => SymBaseChange.pushPt_injective h e).symm
  have su : ∀ {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ)
      (p₀ : Over.mk (t ≫ s) ⟶ G), ∃ p : Over.mk t ⟶ G', Geo.Tor.pushHom h _ p = p₀ := fun h p₀ =>
    ⟨Over.homMk (h.1.lift p₀.left t (Over.w p₀)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  constructor
  · intro H n p₀ q₀ c hn hp hq
    obtain ⟨p, rfl⟩ := su hX p₀
    obtain ⟨q, rfl⟩ := su hY q₀
    exact (key n p q c).1 (H n p q c hn ((pw hX n p).2 hp) ((pw hY n q).2 hq))
  · intro H n p q c hn hp hq
    exact (key n p q c).2 (H n _ _ c hn ((pw hX n p).1 hp) ((pw hY n q).1 hq))

theorem lamEq_weilEq_over_ring : Out.Laws → ∀ (R : Type) [CommRing R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k),
    (LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β)) ∧ (IsDedekindDomain R → Function.Injective β → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β) → LamEq A.L f₁ f₂ B.L g₁ g₂) := by
  intro laws R _ X Y A B f₁ f₂ g₁ g₂ _ _ _ _ k _ _ _ β
  have bc : ∀ P : Out.PolAV (Sp R), ∃ (P' : Out.PolAV (Sp k)) (φ : P'.A.left ⟶ P.A.left),
      IsGrpPullback P'.A P.A (spMap β) φ ∧ LBIso P'.L (P.L.pull φ) := fun P => by
    obtain ⟨P', φ, hφ, -, hm, t, ht⟩ := laws.polBaseChange _ _ (spMap β) P
    refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl
  obtain ⟨X', x, hX, -⟩ := bc X
  obtain ⟨Y', y, hY, -⟩ := bc Y
  obtain ⟨A', a, hA, wL⟩ := bc A
  obtain ⟨B', b, hB, wM⟩ := bc B
  have := A.isAb.comm
  have := B.isAb.comm
  have := A'.isAb.comm
  have := B'.isAb.comm
  obtain ⟨f₁', m₁, e₁⟩ := exists_hom hX hA f₁
  obtain ⟨f₂', m₂, e₂⟩ := exists_hom hY hA f₂
  obtain ⟨g₁', m₃, e₃⟩ := exists_hom hX hB g₁
  obtain ⟨g₂', m₄, e₄⟩ := exists_hom hY hB g₂
  have W := weilEq_iff hX hY hA hB A.isLB B.isLB A'.isLB B'.isLB wL wM e₁ e₂ e₃ e₄ (𝟙 (Sp k))
  rw [Category.id_comp] at W
  let π : Over.mk ((X'.A ⊗ Y'.A).hom ≫ spMap β) ⟶ X.A ⊗ Y.A :=
    lift (Geo.Tor.pushPt hX.1.w (fst X'.A Y'.A)) (Geo.Tor.pushPt hY.1.w (snd X'.A Y'.A))
  have π₁ : π.left ≫ (fst X.A Y.A).left = (fst X'.A Y'.A).left ≫ x := by
    rw [← Over.comp_left, lift_fst]; rfl
  have π₂ : π.left ≫ (snd X.A Y.A).left = (snd X'.A Y'.A).left ≫ y := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hN : (cubeLB A.A ![fst X.A Y.A ≫ f₁, snd X.A Y.A ≫ f₂] A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hN' : (cubeLB B.A ![fst X.A Y.A ≫ g₁, snd X.A Y.A ≫ g₂] B.L).IsLB := DVR.linComb_isLB _ B.isLB _ _
  have hP : (cubeLB A'.A ![fst X'.A Y'.A ≫ f₁', snd X'.A Y'.A ≫ f₂'] A'.L).IsLB := DVR.linComb_isLB _ A'.isLB _ _
  have hP' : (cubeLB B'.A ![fst X'.A Y'.A ≫ g₁', snd X'.A Y'.A ≫ g₂'] B'.L).IsLB := DVR.linComb_isLB _ B'.isLB _ _
  have cA := cube_pull hA A.isLB A'.isLB wL (T' := X'.A ⊗ Y'.A) π.left (Over.w π)
    ![fst X'.A Y'.A ≫ f₁', snd X'.A Y'.A ≫ f₂'] ![fst X.A Y.A ≫ f₁, snd X.A Y.A ≫ f₂] fun i => by
      fin_cases i
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₁, reassoc_of% π₁]
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₂, reassoc_of% π₂]
  have cB := cube_pull hB B.isLB B'.isLB wM (T' := X'.A ⊗ Y'.A) π.left (Over.w π)
    ![fst X'.A Y'.A ≫ g₁', snd X'.A Y'.A ≫ g₂'] ![fst X.A Y.A ≫ g₁, snd X.A Y.A ≫ g₂] fun i => by
      fin_cases i
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₃, reassoc_of% π₁]
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₄, reassoc_of% π₂]
  refine ⟨fun H => W.1 (_root_.GlobalTheory.CM.weilEq_of_lamEq laws k X' Y' A' B' _ _ _ _ m₁ m₂ m₃ m₄ ?_), fun hR hβ H => ?_⟩
  · exact cA.trans hP (Geo.Tor.pull_isLB hN _) hP' (LBIso.trans (Geo.Tor.pull_isLB hN _) (Geo.Tor.pull_isLB hN' _) hP'
      (PowPrimitive.lbIso_linComb H _ _) cB.symm)
  · have H' := GlobalTheory.CM.lamEq_of_weilEq laws k X' Y' A' B' _ _ _ _ m₁ m₂ m₃ m₄ (W.2 H)
    have H'' := cA.symm.trans (Geo.Tor.pull_isLB hN _) hP (Geo.Tor.pull_isLB hN' _) (LBIso.trans hP hP' (Geo.Tor.pull_isLB hN' _) H' cB)
    let F := pullback.fst (X.A ⊗ Y.A).hom (spMap β)
    let p := pullback.snd (X.A ⊗ Y.A).hom (spMap β)
    have wF : F ≫ (X.A ⊗ Y.A).hom = p ≫ spMap β := pullback.condition
    let u : Over.mk p ⟶ X'.A := Over.homMk (hX.1.lift (F ≫ (fst X.A Y.A).left) p
      (by rw [Category.assoc, Over.w, wF])) (hX.1.lift_snd _ _ _)
    let v : Over.mk p ⟶ Y'.A := Over.homMk (hY.1.lift (F ≫ (snd X.A Y.A).left) p
      (by rw [Category.assoc, Over.w, wF])) (hY.1.lift_snd _ _ _)
    have hu : u.left ≫ x = F ≫ (fst X.A Y.A).left := hX.1.lift_fst _ _ _
    have hv : v.left ≫ y = F ≫ (snd X.A Y.A).left := hY.1.lift_fst _ _ _
    have hr : F = (lift u v).left ≫ π.left := by
      refine pullback.hom_ext (f := X.A.hom) (g := Y.A.hom) ?_ ?_
      · show F ≫ (fst X.A Y.A).left = (_ ≫ _) ≫ (fst X.A Y.A).left
        rw [Category.assoc, π₁, ← Category.assoc, ← Over.comp_left, lift_fst, hu]
      · show F ≫ (snd X.A Y.A).left = (_ ≫ _) ≫ (snd X.A Y.A).left
        rw [Category.assoc, π₂, ← Category.assoc, ← Over.comp_left, lift_snd, hv]
    refine _root_.GlobalTheory.IsoDescent.lbIso_of_field R k β hβ (X.A ⊗ Y.A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ X.isAb Y.isAb) _ F p
      (IsPullback.of_hasPullback _ _) _ _ hN hN' ?_
      (LBIso.chartPull (Geo.Tor.chartPullSame _ _ _ _ (lift u v).left fun _ => hr)
        (Geo.Tor.chartPullSame _ _ _ _ (lift u v).left fun _ => hr) H'')
    obtain ⟨t, ht⟩ := exists_gen_cube_one A.isLB (𝟙_ _)
    obtain ⟨t', ht'⟩ := exists_gen_cube_one B.isLB (𝟙_ _)
    exact (cube_zero A.isLB f₁ f₂).symm.trans (Geo.Tor.pull_isLB hN _) (DVR.linComb_isLB _ A.isLB _ _) (Geo.Tor.pull_isLB hN' _)
      (LBIso.trans (DVR.linComb_isLB _ A.isLB _ _) (DVR.linComb_isLB _ B.isLB _ _) (Geo.Tor.pull_isLB hN' _)
        (IsoDescent.lbIso_of_gens A.isLB B.isLB _ _ _ _ t ht t' ht') (cube_zero B.isLB g₁ g₂))

end GlobalTheory.PairingFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegOfLatRankEqZero
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.DegBound

section Lattice

variable {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

end Lattice

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField K] in
theorem eigLat_le {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A)
    (τ : O →+* 𝓞 K) : F.eigLat act τ ≤ F.lieLat :=
  Submodule.span_mono fun _ ⟨u, hu, _⟩ => ⟨u, hu⟩

theorem eigLat_fg {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A)
    (τ : O →+* 𝓞 K) : (F.eigLat act τ).FG := by
  have := isNoetherian_of_fg_of_noetherian _ (LieLattice.lieLat_fg_and_span_eq_top K P F).1
  exact Submodule.FG.of_le_of_isNoetherian (eigLat_le F act τ)

end GlobalTheory.CM.DegBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieEigenbasisGenericFibreCmTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_eigenbasis_fibre : Out.SecTwistSt → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))) (oa : T.pol.OAct (𝓞 E)) (S : Set (E →+* ℂ)) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), oa.act = T.t.act.act → Function.Bijective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → HasType H T.t.act ρ 1 0 → ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ T.pol.A.left) (τ : Fin x.P.g ≃ S), IsFibreOf T.pol x (gmap K) φ ∧ x.P.g = Module.finrank ℚ E / 2 ∧ IsLieType T.pol oa x φ τ lab := by
  intro hT hL E _ _ _ _ H K _ _ T oa S lab ρ hoa hlab hρ hS hty
  classical
  obtain ⟨-, -, h3⟩ := GlobalTheory.CM.splits_basic E
  obtain ⟨hs1, hs2, -⟩ := h3 K
  have hsp : Splits E K := hs1.2 (by
    rw [← Nat.card_eq_of_bijective lab hlab, Nat.card_eq_fintype_card, NumberField.Embeddings.card])
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨F₀⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  have hg : T.g = Module.finrank ℚ E / 2 := by
    simpa using (_root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ T F₀ 1 0 hsp hty hρ).2.2.2.1
  obtain ⟨y, ψ, w, hyg, hψ, hw⟩ := GlobalTheory.KeyPow.exists_keyIn_pullback hT (algebraMap (𝓞 K) K) T.pol (hpos.trans_eq hg.symm)
  have hfib : IsFibreOf T.pol y (spMap (algebraMap (𝓞 K) K)) ψ := ⟨hψ, w, (isGen_iff _).2 hw⟩
  let F : GenFib T.pol := ⟨y.P, ψ, (isFibreOf_iff_isPolFibre _ _ _ _ _ _).1 hfib, y.v, y.basis⟩
  obtain ⟨hrk, hind, -, -, hcard, -⟩ := _root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ T F 1 0 hsp hty hρ
  obtain ⟨r, hr, hr'⟩ := _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat K T.pol F (𝓞 E) T.t.act
  let res : S → (𝓞 E →+* 𝓞 K) := fun t => RingOfIntegers.mapRingHom (lab t)
  have hres : ∀ t (a : 𝓞 E), ((res t a : 𝓞 K) : K) = lab t (a : E) := fun t a => rfl
  have hinj : Function.Injective res := fun s t h => Subtype.ext (hlab.1
    ((hs2 (res t)).unique (fun a => by rw [← h, hres]) (fun a => by rw [hres])))
  have hrt : ∀ t, res t H.rt = ρ := fun t => RingOfIntegers.ext ((hres t _).trans ((hS t).1 t.2))
  have hcS : Nat.card S = Module.finrank ℚ E / 2 := by
    rw [← hcard]
    refine Nat.card_eq_of_bijective (fun t => ⟨res t, hrt t⟩) ⟨fun s t h => hinj (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨τ', hτ', -⟩ := hs2 τ.1
    obtain ⟨t, rfl⟩ := hlab.2 τ'
    refine ⟨⟨t, (hS t).2 (by rw [hτ', τ.2])⟩, Subtype.ext (RingHom.ext fun a => RingOfIntegers.ext ?_)⟩
    exact (hres _ _).trans (hτ' a)
  have hb : ∀ t : S, ∃ b ∈ Submodule.span K (F.eigLat T.t.act (res t) : Set (Fin F.P₀.g → K)), b ≠ 0 := fun t => by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have := hrk (res t)
    rw [latRank, h, if_pos (hrt t), finrank_bot] at this
    exact zero_ne_one this
  choose b hb hb0 using hb
  have hli : LinearIndependent K b := (hind.comp hinj).linearIndependent _ hb hb0
  have hyg' : y.P.g = Module.finrank ℚ E / 2 := hyg.trans hg
  let e : Fin y.P.g ≃ S := (Finite.equivFinOfCardEq (hcS.trans hyg'.symm)).symm
  let M : Matrix (Fin y.P.g) (Fin y.P.g) K := fun i => b (e i)
  have hM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 (hli.comp e e.injective))
  have := y.P.isAb.comm
  obtain ⟨hex, htan, hcomp, -, hbas⟩ := LieComb.lieComb_algebra K y.P.A _ y.v y.basis.1
  choose v' hv' _ using fun i => hex (M i)
  have hv'b : IsLieBasis v' := (hbas M v' y.basis hv').2 hM
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'b⟩, ψ, e, hfib, hyg', fun a i => ?_⟩
  obtain ⟨-, f₀, -, hf₀, hd⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K T.pol F T.pol F (T.t.act.act a) (T.t.act.hom a)
  have h1 : IsLieComb (r a (M i)) y.v (v' i ≫ f₀) := hd _ (hr a) _ _ (hv' i)
  obtain ⟨w', hw', -⟩ := (LieComb.lieComb_algebra K y.P.A _ v' hv'b.1).1 (Pi.single i (lab (e i) (a : E)))
  have h2 := hcomp _ M v' _ w' hv' hw'
  have h3 : r a (M i) = ∑ j, (Pi.single i (lab (e i) (a : E)) : Fin y.P.g → K) j • M j := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp), Pi.single_eq_same]
    exact ((hr' (res (e i)) _).2.1 (hb (e i)) a).trans rfl
  rw [h3] at h1
  refine ⟨w', hw', ?_⟩
  rw [← (hex _).unique h1 h2, hoa]
  exact (congrArg ((v' i).left ≫ ·) hf₀.symm).trans (Category.assoc _ _ _).symm

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Indep

section Linear

variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype J]

theorem finrank_le_sum {N : J → Submodule K V} (h : ⨆ i, N i = ⊤) :
    Module.finrank K V ≤ ∑ i, Module.finrank K (N i) := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  rw [← Module.finrank_directSum]
  exact LinearMap.finrank_le_finrank_of_surjective hs

theorem iSupIndep_of_sum_le {N : J → Submodule K V} (h : ⨆ i, N i = ⊤)
    (hd : ∑ i, Module.finrank K (N i) ≤ Module.finrank K V) : iSupIndep N := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  have he : Module.finrank K (DirectSum J fun i => N i) = Module.finrank K V := by
    rw [Module.finrank_directSum]
    exact le_antisymm hd (finrank_le_sum h)
  exact DirectSum.IsInternal.submodule_iSupIndep
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).2 hs, hs⟩

theorem sum_finrank_eq {N : J → Submodule K V} (hi : iSupIndep N) (h : ⨆ i, N i = ⊤) :
    ∑ i, Module.finrank K (N i) = Module.finrank K V := by
  classical
  rw [← Module.finrank_directSum]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap N)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi h)).finrank_eq

theorem injective_of_sum_eq {W : J → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] {M : ∀ i, W i →ₗ[K] V} (h : ⨆ i, LinearMap.range (M i) = ⊤)
    (hd : ∑ i, Module.finrank K (W i) = Module.finrank K V) (j : J) : Function.Injective (M j) := by
  have hle : ∀ i ∈ (Finset.univ : Finset J), Module.finrank K (LinearMap.range (M i)) ≤ Module.finrank K (W i) :=
    fun i _ => LinearMap.finrank_range_le _
  have he := (Finset.sum_eq_sum_iff_of_le hle).1
    (le_antisymm (Finset.sum_le_sum hle) (hd ▸ finrank_le_sum h)) j (Finset.mem_univ _)
  have := LinearMap.finrank_range_add_finrank_ker (M j)
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

end Linear


open IntCoord in
theorem map_eigLat_le {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) ≤ F'.eigLat a' τ := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem letters_independent : ThetaUnifAV → Out.Laws → IndSt := by
  intro hU hL E _ _ _ H K _ _ ρ σ₁ p q X FA FB M hM N
  classical
  haveI : Finite (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (X.split ▸ Module.finrank_pos)).2
  haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)
  have hρ : ρ ≠ 0 := fun h => by
    have := X.ρ_sq
    rw [h] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hsq : ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = -ρ ↔ ¬ τ H.rt = ρ := fun τ => by
    have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, X.ρ_sq]; simp
    refine ⟨fun h h' => hρ ?_, fun h => (sq_eq_sq_iff_eq_or_eq_neg.1 e).resolve_left h⟩
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination h - h'
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have hA : ∀ b : Bool, (∀ τ : 𝓞 E →+* 𝓞 K, latRank K ((FA b).eigLat (X.A b).t.act τ) =
        if τ H.rt = (if b then ρ else -ρ) then 1 else 0) ∧
      iSupIndep (fun τ : 𝓞 E →+* 𝓞 K =>
        Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K))) ∧
      ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K)) = ⊤ ∧
      (FA b).P₀.g = Module.finrank ℚ E / 2 := by
    rintro (_ | _)
    · obtain ⟨a, b, c, d, -⟩ := _root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ (X.A false) (FA false) 0 1 X.split X.typeM X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA false).fib.1]; simpa using d⟩
      rw [a]
      by_cases h : τ H.rt = ρ
      · rw [if_pos h, if_neg (by simpa [hsq] using h)]
      · rw [if_neg h, if_pos (by simpa [hsq] using h)]
    · obtain ⟨a, b, c, d, -⟩ := _root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ (X.A true) (FA true) 1 0 X.split X.typeP X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA true).fib.1]; simpa using d⟩
      rw [a]
      simp
  have hB : FB.P₀.g = Module.finrank ℚ E / 2 * (p + q) := by
    rw [FB.fib.1]
    exact (_root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ X.B FB p q X.split X.typeB X.ρ_sq).2.2.2.1
  have hsur : ⨆ j, LinearMap.range (M j) = ⊤ :=
    _root_.GlobalTheory.DiffSpan.iSup_range_diff_eq_top hU hL K X.B.pol FB σ₁ (Fin p ⊕ Fin q) (fun j => (X.A j.isLeft).pol) (fun j => FA j.isLeft) X.φ M
      inferInstance (fun j => (X.lin j).1) hM fun y => by
        obtain ⟨x, hx⟩ := X.onto y
        exact ⟨p + q, finSumFinEquiv.symm, fun m => x _, hx⟩
  have hdim : ∑ j : Fin p ⊕ Fin q, Module.finrank K (Fin (FA j.isLeft).P₀.g → K) =
      Module.finrank K (Fin FB.P₀.g → K) := by
    simp [(hA _).2.2.2, hB, mul_comm]
  have hinj := injective_of_sum_eq hsur hdim
  have hspan : ∀ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) =
      (Submodule.span K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2 : Set _)).map (M x.1) := fun x => by
    rw [Submodule.map_span]
    rfl
  have hrk : ∀ x, latRank K (N x) = latRank K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2) := fun x => by
    rw [latRank, hspan]
    exact (Submodule.equivMapOfInjective _ (hinj x.1) _).finrank_eq.symm
  have htop : ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤ := by
    rw [iSup_prod, ← hsur]
    refine iSup_congr fun j => ?_
    rw [← Submodule.map_top, ← (hA j.isLeft).2.2.1, Submodule.map_iSup]
    exact iSup_congr fun τ => hspan (j, τ)
  refine ⟨fun x => map_eigLat_le (X.lin x.1).2 (hM x.1) x.2, fun x => ?_, hinj, iSupIndep_of_sum_le htop ?_, htop⟩
  · rw [hrk, (hA _).1]
  · rw [← hdim, Fintype.sum_prod_type]
    refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [← sum_finrank_eq (hA j.isLeft).2.1 (hA j.isLeft).2.2.1]
    exact Finset.sum_congr rfl fun τ _ => hrk (j, τ)

end GlobalTheory.CM.Indep
end
end

