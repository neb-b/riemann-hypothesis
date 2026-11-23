module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastWeightPositive
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem lastPos_wtA_of_kapIs : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → ∀ i : Fin D.R.m, LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) :=
  fun D T κ h hκ i =>
    GlobalTheory.lastPos_wtA_of_pins D T.Q h.pins _ (inR i) (κ i) (GlobalTheory.HolDict.lastPos_of_kapIs D κ hκ i)

end GlobalTheory.HolRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevAgreesOfIsLift
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftAgrees

open Formalism.IndefR Formalism.L2.DIV

theorem cong_mul {R : Type} [CommRing R] {n : ℕ} (K U : Matrix (Fin n) (Fin n) R) (M : ℕ) (x y w w' : Fin n → R)
    (e : y - K *ᵥ x = M • w) (e' : U *ᵥ x - x = M • w') : y - (K * U) *ᵥ x = M • (w - K *ᵥ w') := by
  rw [smul_sub, ← e, ← Matrix.mulVec_smul, ← e', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

variable {D : D7}

theorem isLift_inv_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g : Formalism.L2.DIV.G0 L.Pg L.r} {κ k : GA D V} (hκ : Lev.IsLevelLift V β L g κ) (hk : Lev.IsLevelLift V β L g k) :
    Lev.IsLevelLift V β L 1 (κ⁻¹ * k) := by
  have h1 : Lev.finE V (κ⁻¹ * k) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ.2.1) hk.2.1
  refine ⟨(GfC V).mul_mem ((GfC V).inv_mem hκ.1) hk.1, h1, ?_⟩
  have h2 := Formalism.L2.DIV.rTup_mul hκ.2.1 h1
  rw [← map_mul, mul_inv_cancel_left, hκ.2.2, hk.2.2] at h2
  exact (mul_eq_left.1 h2.symm)

theorem finCong_one_of_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : Formalism.IndefR.Links.IsSDFrame V β Λ 1) {κ : GA D V}
    (hκ : Lev.finE V κ ∈ St β) : GlobalTheory.Member.FinCong V 1 κ := by
  have hβ : IsFrame β Λ := h.choose_spec.1
  intro z hz
  have h1 := ((GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).1 hκ).1 _ ((GlobalTheory.LiftLevel.latHat_iff_frame h z).1 hz)
  refine ⟨(finHom V κ).1 *ᵥ z - z, sub_mem ?_ hz, (one_smul _ _).symm⟩
  refine (GlobalTheory.LiftLevel.latHat_iff_frame h _).2 ?_
  convert h1 using 1
  funext i
  exact RingHom.map_mulVec (Lev.swapAE D) _ z i


set_option maxHeartbeats 1000000 in
theorem finCong_of_red (P : Formalism.L2.Host.PiBar D.host) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : Formalism.IndefR.Links.IsSDFrame V β Λ 1) {u : GA D V}
    (h1 : u ∈ GfC V) (h2 : Lev.finE V u ∈ St β)
    (h3 : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (∃ k, P.Div k PP) → redFn β PP (Lev.finE V u) = 1) :
    GlobalTheory.Member.FinCong V (D.host.g 0 * D.host.g 1) u := by
  obtain ⟨l, ⟨hM, -⟩, hMb⟩ := Formalism.L2.Pj.levelPb_exists D P.pb P.pb_over
  obtain ⟨Kf, hK⟩ := (GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D V l.M).1
  have hH := (GlobalTheory.Member.finCong_iff_half_and_kfHalf D _ l V).2 Kf hK
  have hN : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ l.Mb := by
    rw [hMb]; exact GlobalTheory.LiftLevel.natCast_mem_prod _
  have hsq : Squarefree l.Mb := (GlobalTheory.CoverHalf.squarefree_span_g D).squarefree_of_dvd
    (Ideal.dvd_span_singleton.2 hN)
  have hu : u ∈ Kf := (GlobalTheory.LiftLevel.mem_level_iff h hK hH hsq l.prod (by rw [hM]; exact hN) u).1
    ⟨h1, h2, fun PP hP => h3 PP (by rw [hMb, GlobalTheory.LiftLevel.prod_le_iff] at hP; exact hP)⟩
  rw [← hM]
  exact ((hK u).1 hu).2

theorem levAgrees_mul {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} {Mh : Ideal (𝓞 D.host.E)}
    {κ u : GA D V} {lev : La →ₗ[𝓞 D.host.E] La} (hκ : GlobalTheory.Member.FinCong V 1 κ) (hu : GlobalTheory.Member.FinCong V M u)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees V ι M Mh κ lev) : GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees V ι M Mh (κ * u) lev := by
  intro a ha
  obtain ⟨w, hw, e⟩ := h a ha
  have hm : ι a ∈ (⊤ : Ideal (𝓞 D.host.E)) • latG V 1 := by
    rw [Submodule.top_smul, ← hι.2]
    exact ⟨a, rfl⟩
  obtain ⟨w', hw', e'⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V u).2 M ⊤).1
    (fun b _ z hz => hu _ (GlobalTheory.Member.halfVec_mem_latHat V b z hz)) _ hm
  refine ⟨w - (finHom V κ).1 *ᵥ w', sub_mem hw ((GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ w' hw'), ?_⟩
  rw [map_mul, Units.val_mul]
  exact cong_mul _ _ M _ _ _ _ e e'

end GlobalTheory.LiftAgrees


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LiftAgrees.levAgrees_of_isLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Formalism.IndefR.Links.Wc D i).rank → D.host.E)) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La), LatEmb (Formalism.IndefR.Links.Wc D i) ι → Formalism.IndefR.FWT.LevIs R i ι (D.host.g 0 * D.host.g 1) Mh lev → ∀ (g : G) (k : GA D (Formalism.IndefR.Links.Wc D i)), Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees (Formalism.IndefR.Links.Wc D i) ι (D.host.g 0 * D.host.g 1) Mh k (lev g) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hIs La _ _ ι Mh lev hι hlev g k hk
  obtain ⟨κ, hκ, hag⟩ := hlev g
  have h1 := (GlobalTheory.LiftLevel.isLift_one_iff (R.βW i) (R.datWp i R.triv)
    (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le rfl _).1 (GlobalTheory.LiftAgrees.isLift_inv_mul hκ hk)
  have h2 := GlobalTheory.LiftAgrees.finCong_of_red R.C.P (hIs.βW i) h1.1 h1.2.1 fun PP hP => h1.2.2 PP ((hIs.Pg PP).2 hP)
  have h3 := GlobalTheory.LiftAgrees.finCong_one_of_St (hIs.βW i) (Formalism.L2.DIV.parLev_St hκ.2.1)
  have h4 := GlobalTheory.LiftAgrees.levAgrees_mul hι h3 h2 hag
  rwa [mul_inv_cancel_left] at h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspFormsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_action_preserves_integral_cusp_forms : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g (f f' : Cu T κ i), (f' : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) → Formalism.IndefR.FWT.IntAll T κ f → Formalism.IndefR.FWT.IntAll T κ f' := by
  first | exact @GlobalTheory.LevActInt.intAll_actLev | exact GlobalTheory.LevActInt.intAll_actLev | (intros; apply GlobalTheory.LevActInt.intAll_actLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    (κ i).LastPos := by
  intro τ a ha
  rw [(h i τ).1 a, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hs : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
  have h1 : ¬ (a : ℕ) < D.R.k - 1 := by omega
  have h2 : (a : ℕ) - (D.R.k - 1) < D.R.m := by omega
  have h3 : (⟨(a : ℕ) - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by show (a : ℕ) - (D.R.k - 1) = i; omega)
  have h4 : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = (a : ℕ) + 1 := by exact_mod_cast ha.symm
  have h5 := (D.hc τ).gap_be i
  simp only [aPl, if_pos a.2, Formalism.L2.NTheta.lamAt, dif_neg h1, dif_pos h2, h3, h4]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem lastPos_wtA_of_pins {D : D7} (Q : Par D) (h : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : w.LastPos) :
    Formalism.L2.Pj.LastPos (Q.Dw j) (wtA w) := by
  intro τ hτ hm
  obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q h.1 τ hτ
  have hmult : (Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold Datum.mult
    have hτ' : (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dif_pos (by omega)]
  unfold wtA
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

section Frame

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {r : ℕ} (hr : W.rank = r)
  (X : Data D.host.E r) {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {p : ℕ}

theorem isInvOf_cart (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsInvOf W hr X (fun τ => x₀ τ.1) (cart M) := by
  intro ρ τ hτ
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  have e : mat (Ψ := X.Ψ) (fun τ => x₀ τ.1) τ = x₀ (tauE D ρ) := by rw [← hτ]; rfl
  rw [e, hx.mul, cart, Formalism.REAL.Jm, torus_x0Mat, hx ρ]
  ext a c
  have hc := c.2
  simp only [sgnM, Matrix.neg_apply, mul_diagonal, reindex_apply, submatrix_apply, hε, hq, arr, sgn,
    finCongr_symm, finCongr_apply, Fin.val_cast]
  split_ifs with h1 h2 h3
  all_goals first | (simp at *; omega) | simp

theorem isBasOf_onb (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsBasOf W hr X hp (fun τ => x₀ τ.1) (onb M) := by
  intro ρ τ hτ k i a hi
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  show _ = x₀ τ.1 _ _
  rw [hτ, hx ρ]
  simp only [x0Mat, reindex_apply, submatrix_apply, hq, finCongr_symm, finCongr_apply, id, Fin.cast_cast, Fin.cast_eq_self]
  congr 1
  apply Fin.ext
  rw [hi]
  rcases k with k | k
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inl k) : Fin r) : ℕ) = X.p0 + k := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1] at h; omega
    · simp only [Fin.val_cast, h1, Sum.elim_inl]; omega
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inr k) : Fin r) : ℕ) = X.p0 - (k + 1) := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1, Sum.elim_inr]; omega
    · simp only [Fin.val_cast, h1] at h; omega

end Frame


end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HatInt

noncomputable section

theorem omegaK_congr {D : D7} {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  refine if_congr (forall₂_congr fun PP hP => ?_) rfl rfl
  rw [h PP hP]

theorem omegaQ_congr {D : D7} {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Q, y PP = y' PP) : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
  unfold omegaQ
  refine dite_congr (propext (forall₂_congr fun PP hP => by rw [h PP hP])) (fun h1 => ?_) (fun _ => rfl)
  refine Finset.prod_congr rfl fun PP _ => ?_
  congr 3
  apply Units.ext
  simp only [IsUnit.unit_spec]
  rw [h PP.1 PP.2]

theorem matrix_map_ringHom_add_smul_sandwich {K S : Type} [CommRing K] [CommRing S] (f : K →+* S) {m n : Type} [Fintype m] [Fintype n]
    (B : Matrix m m S) (C : Matrix n n S) (P : Matrix m m K) (Q : Matrix n n K) (X Y : Matrix m n K) (d : K) :
    B * (P * (X + d • Y) * Q).map f * C = B * (P * X * Q).map f * C + f d • (B * (P * Y * Q).map f * C) := by
  have h2 : ∀ (P Q : Matrix m n K), (P + d • Q).map f = P.map f + f d • Q.map f := by
    intro P Q; ext b a; simp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h2]

theorem uMat_add_smul {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X Y : Fin S.rank → Fin T.rank → D.host.E) (c : D.host.E) :
    FWT.uMat S T βS βT e (fun b => X b + c • Y b) =
      fun b a => FWT.uMat S T βS βT e X b a + eToEAf D (D.sp.cm.sig c) * FWT.uMat S T βS βT e Y b a := by
  have h1 : (Matrix.of fun b a => D.sp.cm.sig ((X b + c • Y b) a)) =
      (Matrix.of fun b a => D.sp.cm.sig (X b a)) + D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a; simp
  funext b a
  have h2 := congrFun (congrFun (matrix_map_ringHom_add_smul_sandwich (eToEAf D) (βS⁻¹).val βT.val S.gram⁻¹ T.gram
    (Matrix.of fun b a => D.sp.cm.sig (X b a)) (Matrix.of fun b a => D.sp.cm.sig (Y b a)) (D.sp.cm.sig c)) b) a
  rw [← h1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h2
  have h3 := congrArg (fun u => toEAf D e * u) h2
  simp only [mul_add] at h3
  rw [mul_left_comm] at h3
  exact h3

theorem subring_reduction_add_mul_killed {S k : Type} [CommRing S] [CommRing k] (O : Subring S) (f : O →+* k) (x y : S) (hx : x ∈ O) (hy : y ∈ O)
    (c : O) (hc : f c = 0) :
    (if h : x + (c : S) * y ∈ O then f ⟨x + (c : S) * y, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hmem : x + (c : S) * y ∈ O := add_mem hx (mul_mem c.2 hy)
  rw [dite_eq_left hmem, dite_eq_left hx]
  have : (⟨_, hmem⟩ : O) = ⟨x, hx⟩ + c * ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _), map_mul, hc, zero_mul, add_zero]

theorem redM_add_smul {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N N' : Matrix (Fin b) (Fin a) (EAf D))
    (hN : Datum.IsIntM N) (hN' : Datum.IsIntM N') (s : 𝓞 D.host.E) (hs : s ∈ PP.asIdeal) :
    Datum.redM PP (fun i j => N i j + eToEAf D (s : D.host.E) * N' i j) = Datum.redM PP N := by
  funext i j
  have h0 : ((Formalism.L2.DIV.oToS D.host.F D.host.E s : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      eToEAf D (s : D.host.E) := by
    unfold Formalism.L2.DIV.oToS eToEAf
    rw [RingHom.codRestrict_apply]
    rfl
  rw [← h0]
  unfold Datum.redM
  exact subring_reduction_add_mul_killed _ (Formalism.L2.DIV.resS D.host.F PP) _ _ (hN i j) (hN' i j) _
    (by rw [Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hs])

theorem sig_bar {D : D7} (H : Geo.Tor.Host D.host.E) (s : 𝓞 D.host.E) :
    D.sp.cm.sig ((H.bar s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
  rw [H.bar_eq]
  exact IsCMField.complexConj_apply_apply D.host.E (s : D.host.E)

theorem dvd_of_invariant {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    (l : Geo.Tor.Level H) {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) (hq : hatC l φ q ≠ 0)
    (z : Fin n → Dw.La) (hφ : ∀ x, φ (x + fun b => Submodule.Quotient.mk (z b)) = φ x) :
    (l.M : ℤ) ∣ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hp := Complex.isPrimitiveRoot_exp l.M hM
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) with hζ
  have h0 : ζ ≠ 0 := hp.ne_zero hM
  have hrep : ∀ y : LevQc Dw l, Submodule.Quotient.mk (qRep y) = y := fun y =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ y)
  have key : hatC l φ q = ζ ^ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) * hatC l φ q := by
    unfold hatC
    rw [mul_finsum, ← finsum_comp_equiv (Equiv.addRight (fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)))]
    refine finsum_congr fun x => ?_
    simp only [Equiv.coe_addRight]
    rw [hφ, mul_left_comm, ← zpow_add₀ h0]
    congr 1
    have hd := LevelPairing.pairL_congr (l := l)
      (fun b => qRep ((x + fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)) b)) (fun b => z b + qRep (x b))
      (fun b => levRep (q b)) (fun b => levRep (q b))
      (fun b => (Submodule.Quotient.eq _).1 (by
        rw [hrep, Submodule.Quotient.mk_add, hrep, add_comm]; rfl)) (fun b => by simp)
    have ha : Formalism.L2.Pj.pairL (l := l) (fun b => z b + qRep (x b)) (fun b => levRep (q b)) =
        Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) +
          Formalism.L2.Pj.pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)) := by
      simp [Formalism.L2.Pj.pairL, Finset.sum_add_distrib]
    rw [← ha]
    have := (hp.zpow_eq_one_iff_dvd _).2 hd
    rwa [zpow_sub₀ h0, div_eq_one_iff_eq (zpow_ne_zero _ h0)] at this
  rw [← hp.zpow_eq_one_iff_dvd]
  exact (mul_left_eq_self₀.1 key.symm).resolve_right hq

theorem smul_eq_of_hatC_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    have h1 := dvd_of_invariant l₂ φ q hq (fun b' => H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b') (by
      intro x
      obtain ⟨x, rfl⟩ : ∃ x' : Fin (Vc D i).rank → Dw.La, x = fun b => Submodule.Quotient.mk (x' b) :=
        ⟨fun b => qRep (x b), funext fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm⟩
      have e1 := (he (fun b' => x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')).2
      have e2 := (he x).2
      simp only [RingHom.id_apply] at e1 e2
      have e3 : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b' => ι (x b')) := by
        intro PP hP
        have e4 : (fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
            fun b' => ι (x b') + ((H.bar s : 𝓞 D.host.E) : D.host.E) •
              ι ((Pi.single b w : Fin (Vc D i).rank → Dw.La) b') := by
          funext b'
          rw [map_add (f := _), map_smul]
          rfl
        rw [e4, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he x).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => e3 PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => e3 PP (Or.inr hP)), ← e2] at e1
      exact e1)
    unfold Formalism.L2.Pj.pairL at h1
    rw [Finset.sum_eq_single b] at h1
    · simpa [Dw.adj, LevelPairing.bar_bar] using h1
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have h2 := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at h2
    have h3 := hdvd y
    have : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by linarith
    rw [this]; exact h3.neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩

end

end GlobalTheory.HatInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.Transl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem lifts (hL : R.toLevCh.Is A.μ0) : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  have h := hL.βW i
  obtain ⟨c, hc⟩ := h
  exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty _ _ _ _ _ hc rfl
    (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg)

theorem levChi_flag (k : GA D (Wc D i)) : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) k)) = 1 := Lev.subgroupCharExtension_one_apply _ _
  unfold Lev.levChi levFn
  rw [h2, show (Lev.flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (Lev.flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem hasType (hW : R.models_HW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    Lev.HasType (Wc D i) (R.βW i) (Lev.flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := (hW i σ).2.1.le (LinearMap.mem_range_self _ y)
  exact fun κ hκ h => ((GlobalTheory.MultMem.mem_mult_iff ..).1 hm).lev v κ hκ h

theorem transl (hW : R.models_HW) (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (g : G) (k : GA D (Wc D i))
    (hk : IsLiftW R i g k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) (h : GA D (Wc D i)) :
    (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k) := by
  have h1 := Lev.level_action_spec (hasType R i hW σ y v) ⟨k, hk⟩ k hk h
  have h2 : (R.HW i σ).e (R.gW i σ g y) v h =
      Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i σ).e y v) h :=
    congrArg (fun U : MMap (R.MW i σ) => U v h) (hg i σ g y)
  refine h2.trans (h1.trans ?_)
  rw [levChi_flag, inv_one, one_mul]

theorem sum_apply_eq {G X Y : Type} [Fintype G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ev : X →ₗ[ℂ] Y) (c : G → ℂ) (a : G → Y →ₗ[ℂ] Y) (b : G → X) (y : Y) (h : ∀ g, ev (b g) = a g y) :
    (∑ g, c g • a g) y = ev (∑ g, c g • b g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h]

theorem proj (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v :=
  sum_apply_eq
    (({ toFun := fun U => U v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      MMap (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)) ∘ₗ (R.HW i σ).e)
    (RealDat.eC (A := A) σ) (fun g => actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (fun g => R.gW i σ g y)
    ((R.HW i σ).e y v) fun g => congrArg (fun U : MMap (R.MW i σ) => U v) (hg i σ g y)

end GlobalTheory.GalLift.Transl

namespace GlobalTheory.GalLift

end GlobalTheory.GalLift

end
end

