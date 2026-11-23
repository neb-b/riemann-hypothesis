module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSixth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseKernel
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnCmp


open Classical in
theorem exists_baseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∃ ω φ, IsBaseKernel R i v (ownAt D v) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu
  obtain ⟨ψw, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hδ : R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = R.xiH (R.mu v) * ψw⁻¹ := by rw [hxi, mul_inv_cancel_right]
  have htame : ∀ P, (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TameAt P := by
    intro P
    unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
    intro x hx hle
    have loc_mul (a b : Formalism.L2.Host.HChar D.host.E) :
        (a * b).loc P x = a.loc P x * b.loc P x := rfl
    have loc_inv (a : Formalism.L2.Host.HChar D.host.E) :
        (a⁻¹).loc P x = (a.loc P x)⁻¹ := rfl
    rw [hδ, loc_mul, loc_inv, hL.xi_tame (R.mu v) P x hx hle, hψ.tame P x hx hle,
      inv_one, mul_one]
  have htriv : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TrivOn D.host.F := by
    rw [hδ]; exact (hL.xi_triv (R.mu v)).mul hψ.triv.inv
  have hunit : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).IsUnitary := by
    obtain ⟨n, hn, hno⟩ := hL.xi_fin (R.mu v)
    obtain ⟨a, ha⟩ := hψ.ord
    refine Formalism.L2.Host.HChar.isUnitary_of_order (n := n * Formalism.EigenvalueLevelCeiling.plc v ^ a)
      (Nat.mul_pos hn (pow_pos (Formalism.EigenvalueLevelCeiling.plc_prime v).pos a)) ?_
    show _ ^ (n * _) = 1
    rw [hδ, mul_pow, inv_pow, pow_mul, hno, one_pow, one_mul, mul_comm n, pow_mul, ha, one_pow, inv_one]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CharTransport.exists_chrEq D _ hunit
  have hF : ∀ a, χ (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hχ htriv
  have hr0 : ResEta D χ 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ a => by rw [hF a, pow_zero]⟩
  have h0 := hC.thP.ωP i A.μ0
  obtain ⟨ω, hω, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D R.ψ h0.std _ _ _ _ χ χ _ h0 hχ.1 hχ.1 hr0 hr0
  have hx0 : R.xi A.μ0 = 1 :=
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x
  have hω' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := by
    convert hω using 2
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
      exact mul_right_comm _ _ _
  choose ξR hξR using fun PP => GlobalTheory.exists_isRes_of_tameAt D _ PP (htame PP)
  have hsub : placesOver R (R.mu v) (ownAt D v) ⊆ R.Q (R.mu v) := Finset.filter_subset _ _
  obtain ⟨e0, he0, -⟩ := (hC.thP.vP i (R.mu v)).2
  have hsub' : R.Pg ∪ placesOver R (R.mu v) (ownAt D v) ⊆ R.Pg ∪ R.Q (R.mu v) := Finset.union_subset_union le_rfl hsub
  have hnc : ∀ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), ∀ P' ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v),
      ¬ Lev.IsConjPl P P' := fun P hP P' hP' =>
    GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0 P (hsub' hP) P' (hsub' hP')
  obtain ⟨cV, hcV⟩ := hL.βV i
  obtain ⟨cW, hcW⟩ := hL.βW i
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i)
    (R.ΛW i) (R.βV i) (R.βW i) R.Pg (placesOver R (R.mu v) (ownAt D v)) ξR (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcV)
    (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcW) hcV.1 hcW.1 ((Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL (R.mu v)).mono_right hsub)
    (Formalism.IndefR.Fin.idemSum_of_noConj _ hnc) (R.vacP i) (hC.thP.vP i (R.mu v)).1
  refine ⟨ω, φ, ?_⟩
  unfold IsBaseKernel IsKernel
  exact ⟨χ, ξR, hχ, fun PP _ => hξR PP, hω', hφ⟩

end GlobalTheory.OnCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem exists_rest_tens_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)),
    ∀ φ ∈ SB (κ → Fv F v), φ ≠ 0 →
    ∃ r : (κ → AF F) → ℂ, Rest (evFin F v) φ r ∧ tens (evFin F v) φ r ≠ 0 := by
  intro F _ _ κ _ v φ hφ hne
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  refine ⟨R, hR φ hφ, fun h => ?_⟩
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (x i)) :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have h1 := (hR φ hφ).1 0 _ hz
  rw [zero_add] at h1
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (x i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, h1, Pi.zero_apply] at e
  exact mul_ne_zero hx hR0 e

end GlobalTheory.InertSph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstEqInvChar
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Datum
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.PinCoord

theorem mk_sum_smul {O La : Type} [CommRing O] [AddCommGroup La] [Module O La] (J : Submodule O La) {r : ℕ}
    (c : Fin r → O) (x : Fin r → La) : (Submodule.Quotient.mk (∑ b, c b • x b) : La ⧸ J) =
      ∑ b, c b • (Submodule.Quotient.mk (x b) : La ⧸ J) := by
  change J.mkQ _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

theorem isUnit_det_of_span : ∀ {O La ι : Type} [CommRing O] [AddCommGroup La] [Module O La] (P : Finset ι) (k : ι → Type) [∀ i, CommRing (k i)] (φ : ∀ i, O → k i) {r : ℕ} (ρ : ∀ i, Fin r → La →+ k i), (∀ i a c x, ρ i a (c • x) = φ i c * ρ i a x) → ∀ (J : Submodule O La), (∀ x, x ∈ J → ∀ i ∈ P, ∀ a, ρ i a x = 0) → (∀ t : ∀ i, Fin r → k i, ∃ x, ∀ i ∈ P, ∀ a, ρ i a x = t i a) → ∀ x : Fin r → La, Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) = ⊤ → ∀ i ∈ P, IsUnit (Matrix.of fun b a => ρ i a (x b)).det := by
  intro O La ι _ _ _ P k _ φ r ρ hs J hJ hon x hx i hi
  classical
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
  intro t
  obtain ⟨v, hv⟩ := hon (Pi.single i t)
  have hm : (Submodule.Quotient.mk v : La ⧸ J) ∈ Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) :=
    hx ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hm
  have hw : v - ∑ b, c b • x b ∈ J := by
    rw [← Submodule.Quotient.eq]
    rw [← hc]
    exact (mk_sum_smul J c x).symm
  refine ⟨fun b => φ i (c b), funext fun a => ?_⟩
  have h1 := hJ _ hw i hi a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, sub_eq_zero] at h1
  simp only [hs] at h1
  have h2 := hv i hi a
  rw [Pi.single_eq_same] at h2
  rw [← h2, h1]
  simp [Matrix.vecMul, dotProduct]

theorem span_of_isUnit_det : ∀ {O La ι : Type} [CommRing O] [AddCommGroup La] [Module O La] (P : Finset ι) (k : ι → Type) [∀ i, CommRing (k i)] (φ : ∀ i, O → k i), (∀ t : ∀ i, k i, ∃ c, ∀ i ∈ P, φ i c = t i) → ∀ {r : ℕ} (ρ : ∀ i, Fin r → La →+ k i), (∀ i a c x, ρ i a (c • x) = φ i c * ρ i a x) → ∀ (J : Submodule O La), (∀ x, (∀ i ∈ P, ∀ a, ρ i a x = 0) → x ∈ J) → ∀ x : Fin r → La, (∀ i ∈ P, IsUnit (Matrix.of fun b a => ρ i a (x b)).det) → Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) = ⊤ := by
  intro O La ι _ _ _ P k _ φ hcrt r ρ hs J hJ x hu
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective J q
  have he : ∀ i, ∃ e : Fin r → k i, i ∈ P → Matrix.vecMul e (Matrix.of fun b a => ρ i a (x b)) = fun a => ρ i a v := by
    intro i
    by_cases hi : i ∈ P
    · have hs' := Matrix.vecMul_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hu i hi))
      obtain ⟨e, he⟩ := hs' (fun a => ρ i a v)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose e he using he
  choose c hc using fun b : Fin r => hcrt fun i => e i b
  have hmem : v - ∑ b, c b • x b ∈ J := hJ _ fun i hi a => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, sub_eq_zero]
    simp only [hs, hc _ i hi]
    have := congrFun (he i hi) a
    rw [← this]
    simp [Matrix.vecMul, dotProduct]
  have e1 : (Submodule.Quotient.mk v : La ⧸ J) = ∑ b, c b • (Submodule.Quotient.mk (x b) : La ⧸ J) := by
    rw [(Submodule.Quotient.eq J).2 hmem]
    exact mk_sum_smul J c x
  rw [e1]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem adjoint_comp_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d), (∀ u v : Dw.La, (d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v)))) → ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, (∀ x, (Submodule.Quotient.mk (f x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) → (∀ x x', (d.pd : ℤ) ∣ Dw.EF (f x) (f x') - Dw.EF x x') → ∀ a : Dw.La, kst (Submodule.Quotient.mk (f a)) = (Submodule.Quotient.mk a : LaJ Xo c d) := by
  intro E _ _ _ H Dw l Xo c n d hd k kst hk f hf1 hf2 a
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  have hp := GlobalTheory.DatumInverseCharacter.half_prod hM hMb
  have hc := GlobalTheory.DatumInverseCharacter.cHalf_mem (H := H) d.I
  have hc1 := (GlobalTheory.HalfPairing.cHalf_spec (H := H) d.I hI).2
  have hN : d.pd ≠ 0 := by
    intro h
    have := d.l₂.three_le
    rw [hM, h] at this
    omega
  have hpd : (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have : Ideal.span {(d.pd : 𝓞 E)} ≤ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := hp ▸ Ideal.mul_le_right
    exact this (Ideal.subset_span rfl)
  rw [← GlobalTheory.HalfPairing.qRep_mk (kst (Submodule.Quotient.mk (f a))), Submodule.Quotient.eq]
  set z := qRep (kst (Submodule.Quotient.mk (f a) : LaJ Xo c d)) with hz
  set t := cHalf H d.I with ht
  have hdiv : ∀ v, (d.pd : ℤ) ∣ Dw.EF (z - a) (t • v) := by
    intro v
    have h1 := hk (f a) v
    have h2 := GlobalTheory.DatumInverseCharacter.dvd_right Dw hp hc (f a)
      (w := qRep (k (Submodule.Quotient.mk v)) - f v) (by
        rw [← Submodule.Quotient.eq, GlobalTheory.HalfPairing.qRep_mk, hf1])
    have h3 := hf2 a (t • v)
    rw [map_smul] at h3
    rw [smul_sub, map_sub] at h2
    have := dvd_add (dvd_add h1 h2) h3
    rw [map_sub, LinearMap.sub_apply]
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  have h4 : H.bar t • (z - a) ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) :=
    GlobalTheory.DatumInverseCharacter.mem_of_modN Dw hpd (GlobalTheory.DatumInverseCharacter.modN_of_dvd Dw (Nat.pos_of_ne_zero hN)
      fun q => by rw [Dw.adj, GlobalTheory.DatumInverseCharacter.bar_bar]; exact hdiv q)
  have h5 : (H.bar t - 1) • (z - a) ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
    refine Submodule.smul_mem_smul ?_ trivial
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc1
    rwa [map_sub, map_one] at this
  have := sub_mem h4 h5
  rwa [sub_smul, one_smul, sub_sub_cancel] at this

theorem topL_mul {κ : Type} [CommRing κ] {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) κ) (B : Matrix (Fin r) (Fin r) κ) :
    topL r (A * B) = topL r A * B := by
  ext i j
  simp only [topL, Matrix.mul_apply, dif_pos (And.intro (lt_of_lt_of_le i.2 hrn) j.2), i.2, j.2, true_and,
    lt_of_lt_of_le i.2 hrn, Fin.is_lt, dite_true]

theorem topL_of {κ : Type} [Zero κ] {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) κ) :
    topL r A = Matrix.of fun b a => A (Fin.castLE hrn b) a := by
  ext i j
  simp only [topL, dif_pos (And.intro (lt_of_lt_of_le i.2 hrn) j.2), Matrix.of_apply]
  rfl

theorem image_eq_range {α : Type} {n r : ℕ} (hrn : r ≤ n) (x : Fin n → α) :
    x '' {b | b.val < r} = Set.range fun a : Fin r => x (Fin.castLE hrn a) := by
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.val, hb⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, a.2, rfl⟩

theorem exists_const_eq_inv_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (xJ : Fin n → LaJ Xo c d), d.PhiPin ph ψ xJ → ∀ (r : ℕ), Dw.p + Dw.q = r → r ≤ n → ∀ (Q : Finset (Pl E)) (ξ : ∀ P : Pl E, (kP P)ˣ →* ℂˣ) (ρ : ∀ P : Pl E, Fin r → Dw.La →+ kP P), (∀ (P : Pl E) (a : Fin r) (t : 𝓞 E) (x : Dw.La), ρ P a (t • x) = Ideal.Quotient.mk P.asIdeal (H.bar t) * ρ P a x) → (∀ x : Dw.La, x ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) ↔ ∀ P ∈ Q, ∀ a, ρ P a x = 0) → (∀ t : ∀ P : Pl E, Fin r → kP P, ∃ x, ∀ P ∈ Q, ∀ a, ρ P a x = t P a) → (∀ k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, ∃ (f : Dw.La →ₗ[𝓞 E] Dw.La) (y : ∀ P : Pl E, GL (Fin r) (kP P)), (∀ x, (Submodule.Quotient.mk (f x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) ∧ (∀ x x', (d.pd : ℤ) ∣ Dw.EF (f x) (f x') - Dw.EF x x') ∧ (∀ P ∈ Q, ∀ x : Fin n → Dw.La, (Matrix.of fun b a => ρ P a (x b)) = (Matrix.of fun b a => ρ P a (f (x b))) * (y P).val) ∧ (((ψ k : c.Fˣ) : c.F) : ℂ) = ∏ P ∈ Q, ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ)) → ∃ u : ∀ P : Pl E, (kP P)ˣ, ∀ x : Fin n → Dw.La, (if h : ∀ P ∈ Q, IsUnit (topL r (Matrix.of fun b a => ρ P a (x b))).det then ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) else 0) = (∏ P ∈ Q, (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)) * ((ph (fun b => Submodule.Quotient.mk (x b)) : c.F) : ℂ) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin r hr hrn Q ξ ρ hs hker hon hfy
  subst hr
  obtain ⟨hc1, hc2, hc3, hc4, hc5, -⟩ := hpin
  obtain ⟨-, huniq, adj, -, hadj⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  have hcrt : ∀ t : ∀ P : Pl E, kP P, ∃ c, ∀ P ∈ Q, Ideal.Quotient.mk P.asIdeal (H.bar c) = t P := fun t => by
    obtain ⟨c, hc⟩ := GlobalTheory.BasePoint.crt_places Q t
    exact ⟨H.bar.symm c, fun P hP => by rw [RingEquiv.apply_symm_apply]; exact hc P hP⟩

  have hspan : ∀ x : Fin n → Dw.La, Submodule.span (𝓞 E) ((fun b => (Submodule.Quotient.mk (x b) : LaJ Xo c d)) ''
      {b | b.val < Dw.p + Dw.q}) = ⊤ ↔ ∀ P ∈ Q, IsUnit (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (x b))).det := by
    intro x
    rw [image_eq_range hrn]
    simp only [topL_of hrn, Matrix.of_apply]
    exact ⟨isUnit_det_of_span Q (fun P => kP P) (fun P c => Ideal.Quotient.mk P.asIdeal (H.bar c)) ρ hs _
        (fun y hy => (hker y).1 hy) hon (fun a => x (Fin.castLE hrn a)),
      span_of_isUnit_det Q (fun P => kP P) (fun P c => Ideal.Quotient.mk P.asIdeal (H.bar c)) hcrt ρ hs _
        (fun y hy => (hker y).2 hy) (fun a => x (Fin.castLE hrn a))⟩
  set X₀ : Fin n → Dw.La := fun b => qRep (xJ b) with hX₀
  have hX₀mk : (fun b => (Submodule.Quotient.mk (X₀ b) : LaJ Xo c d)) = xJ :=
    funext fun b => GlobalTheory.HalfPairing.qRep_mk (xJ b)
  have hX₀u := (hspan X₀).1 (by rw [hX₀mk]; exact hc5)
  let u : ∀ P : Pl E, (kP P)ˣ := fun P =>
    if h : IsUnit (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (X₀ b))).det then h.unit else 1
  have hu : ∀ P ∈ Q, ((u P : (kP P)ˣ) : kP P) = (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (X₀ b))).det :=
    fun P hP => by simp only [u, dif_pos (hX₀u P hP), IsUnit.unit_spec]
  refine ⟨u, fun x => ?_⟩
  split_ifs with h
  ·
    have hxs := (hspan x).2 h
    rw [image_eq_range hrn] at hxs
    have hJs : Submodule.span (𝓞 E) (Set.range fun a : Fin (Dw.p + Dw.q) => xJ (Fin.castLE hrn a)) = ⊤ := by
      rw [← image_eq_range hrn]; exact hc5
    obtain ⟨kst, hkst, -⟩ := huniq _ _ hJs hxs
    have hk := (hadj (adj kst) kst).2 rfl
    have hph : ph (fun b => Submodule.Quotient.mk (x b)) = (((ψ (adj kst))⁻¹ : c.Fˣ) : c.F) := by
      have e1 : ph (fun b => Submodule.Quotient.mk (x b)) = ph (fun b => kst (xJ b)) :=
        hc1 _ _ fun b hb => (hkst ⟨b.val, hb⟩).symm
      rw [e1, hc3 (adj kst) kst hk xJ, hc4, mul_one]
    obtain ⟨f, y, hf1, hf2, hf3, hf4⟩ := hfy (adj kst)
    have hC := adjoint_comp_isometry E H Dw l Xo c n d hd (adj kst) kst hk f hf1 hf2
    have hfx : ∀ b : Fin n, b.val < Dw.p + Dw.q → ∀ P ∈ Q, ∀ a, ρ P a (f (x b)) = ρ P a (X₀ b) := by
      intro b hb P hP a
      have e2 : (Submodule.Quotient.mk (f (x b)) : LaJ Xo c d) = Submodule.Quotient.mk (X₀ b) := by
        apply kst.injective
        rw [hC, congrFun hX₀mk b]
        exact (hkst ⟨b.val, hb⟩).symm
      have := (hker (f (x b) - X₀ b)).1 ((Submodule.Quotient.eq _).1 e2) P hP a
      rwa [map_sub, sub_eq_zero] at this
    have hunit : ∀ (P : Pl E) (hP : P ∈ Q), (h P hP).unit = u P * Matrix.GeneralLinearGroup.det (y P) := by
      intro P hP
      apply Units.ext
      rw [IsUnit.unit_spec, Units.val_mul, hu P hP, Matrix.GeneralLinearGroup.val_det_apply, hf3 P hP x,
        topL_mul hrn, Matrix.det_mul]
      congr 2
      rw [topL_of hrn, topL_of hrn]
      ext b a
      exact hfx _ (by simp) P hP a
    have hL : ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) =
        (∏ P ∈ Q, (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)) * (∏ P ∈ Q, ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ))⁻¹ := by
      calc ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ)
          = ∏ P ∈ Q.attach, ((((ξ P.1 (u P.1))⁻¹ : ℂˣ) : ℂ) *
              (((ξ P.1 (Matrix.GeneralLinearGroup.det (y P.1)) : ℂˣ) : ℂ))⁻¹) :=
            Finset.prod_congr rfl fun P _ => by
              rw [hunit P.1 P.2, map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val (ξ P.1 (Matrix.GeneralLinearGroup.det (y P.1)))]
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
            Finset.prod_attach Q (fun P => (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)),
            Finset.prod_attach Q (fun P => ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ))]
    rw [hL, ← hf4, hph, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
  ·
    have h0 : ph (fun b => Submodule.Quotient.mk (x b)) = 0 := by
      by_contra hne
      exact h ((hspan x).1 (hc2 _ hne))
    rw [h0]
    simp

end GlobalTheory.PinCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f := by
  intro hci D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO t x
  have hj := inR i
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨-, -, -, -, hr, -, hr1, -, -, -, hDom, -, hLast⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i _ rfl
    (T.dict ((i : ℕ) + 1) T.toCore.σ₀ 1).1
  obtain ⟨hι, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ hj _ hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨hxi, n, hn, hxn⟩ := GlobalTheory.ClassSumRule.xi_laws hR.lev (hO.tuple t).xi
  obtain ⟨hd, hA, -⟩ := hO.cov t
  have hpq := hr ▸ hr1
  have hN : 0 < m * n := Nat.mul_pos hm hn
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  have hxN : ∀ h : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) ^ (m * n) = 1 := fun h => by
    rw [mul_comm, pow_mul, hxn, one_pow]
  obtain ⟨_, _, _, hfam⟩ := hR.fam.tie
  obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.ClassSumRule.exists_char hR.lev (O.dδ t) hd hι (hr.symm.trans (rank_Wc i).symm) hpq
    (hO.tuple t).half (fun P hP z => by
      obtain ⟨a, ha⟩ := GlobalTheory.RationalValues.xiR_mem R hR.lev hR.fam.pl_onto hR.fam.muVal hfam.ok i (tup t) P hP z
      rw [← ha, ← hO.lift.field]
      exact (O.jL a).2) (hO.tuple t).xi (hO.tuple t).phi
  obtain ⟨f, hf, hcls, -⟩ := GlobalTheory.ClsVal.exists_cusp_isThClsD_unique hci _ _ _ _ _ O.c' _ (O.dδ t) _
    (unfBC O.hle (T.U ((i : ℕ) + 1))) hr1
    (fun σ hσ => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.laws.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ))
    hT.laws.pins.2.1.2 (fun _ => hO.cov t)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ _ _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN _ _ c0 hcN (hv t))
    ψ (GlobalTheory.ClassSumRule.psiTie_of_values _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN hxi _ _ c0 hcN (hv t) ψ hψ)
    _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) hDom hLast
    (fun k => hw _ (hO.w t k)) (hO.reps t).1 (by
      obtain ⟨-, _, h⟩ := hO.io
      exact h.2.2.1.le) x
  exact ⟨f, hf, hcls⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.AdelicU

namespace GlobalTheory.LocPlTau

theorem exists_splitPrime_locPl : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (_hL : L.Is μ₀) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)), (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) →
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → splitPrime τ = w := by
  intro D T L sc G μ₀ hL t v ⟨w, hw, hv⟩
  subst hv
  obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hex : ∃ ρ : D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F)), splitPrime ρ = w := by
    by_cases e : w = splitPrime τ
    · exact ⟨τ, e.symm⟩
    · exact (existsUnique_splitPrime_eq hc e rfl (splitPrime_under τ)).exists
  obtain ⟨ρ, hρ⟩ := hex
  exact ⟨ρ, fun w' hw' h => hρ.trans (GlobalTheory.FunObj.Good.under_injOn hL G t hw hw' h.symm)⟩

end GlobalTheory.LocPlTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ := by
  first | exact @GlobalTheory.VacAny.exists_isVac_any_darboux | exact GlobalTheory.VacAny.exists_isVac_any_darboux | (intros; apply GlobalTheory.VacAny.exists_isVac_any_darboux <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalHeisenbergEndomorphismStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_local_heisenbergEndomorphism : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∃ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) := by
  first | exact @GlobalTheory.InertRho.exists_rho | exact GlobalTheory.InertRho.exists_rho | (intros; apply GlobalTheory.InertRho.exists_rho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataOverRowFieldConditionsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  first | exact @GlobalTheory.PinsOverClauses.pinsOverL_of_clauses | exact GlobalTheory.PinsOverClauses.pinsOverL_of_clauses | (intros; apply GlobalTheory.PinsOverClauses.pinsOverL_of_clauses <;> assumption)
end

