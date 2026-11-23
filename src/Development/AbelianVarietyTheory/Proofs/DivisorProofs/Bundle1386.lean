module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeigh
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.MovedLat

open Formalism.UG

theorem htFin_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) :
    htFin F v (bc (compFin F E v) g⁻¹) = htFin F v (bc (compFin F E v) g) := by
  rw [map_inv]; exact htOf_inv _ _

theorem finprod_htFin_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) :
    ∏ᶠ v, htFin F v (bc (compFin F E v) g) ≤ heightGL F g :=
  le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)

end GlobalTheory.MovedLat

open Formalism.UG

theorem GlobalTheory.MovedLat.exists_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  intro F E _ _ _ _ _ n d κ _ _ e N hN
  classical
  let f1 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.fst (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  let f2 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.snd (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  choose K1 hK1f hK1 hK1b using fun j => GlobalTheory.LinFormBound.main (f1 j)
  choose K2 hK2f hK2 hK2b using fun j => GlobalTheory.LinFormBound.main (f2 j)
  let Y : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i => e.symm (0, Pi.single i 1)
  choose Kx hKxf hKx hKxb using fun i => GlobalTheory.FixedBound.exists_entry_absFin_bound (Y i)
  let Kc : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ j, K1 j v * K2 j v) * ∏ i, Kx i v
  have hKc1 : ∀ v, 1 ≤ Kc v := fun v =>
    one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.one_le_prod' fun i _ => hKx i v)
  have hKcf : (Function.mulSupport Kc).Finite := by
    refine ((Set.finite_iUnion fun j => (hK1f j).union (hK2f j)).union (Set.finite_iUnion hKxf)).subset ?_
    refine (Function.mulSupport_mul _ _).trans (Set.union_subset_union ?_ ?_)
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨j, -, hj⟩ := hv
      exact ⟨j, Function.mulSupport_mul _ _ hj⟩
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨i, -, hi⟩ := hv
      exact ⟨i, hi⟩
  have hP1 : ∀ v, ∏ j, K1 j v * K2 j v ≤ Kc v := fun v =>
    le_mul_of_one_le_right' (Finset.one_le_prod' fun i _ => hKx i v)
  have hP2 : ∀ v, ∏ i, Kx i v ≤ Kc v := fun v =>
    le_mul_of_one_le_left' (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
  have hK1c : ∀ v i j, K1 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_right' (hK2 j v)) le_rfl
  have hK2c : ∀ v i j, K2 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_left' (hK1 j v)) le_rfl
  let C0 : ℝ≥0 := ∏ᶠ v, Kc v
  refine ⟨N * C0, 1, fun g h => ?_⟩
  let Hg : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) g)
  let Hh : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) h)
  have hgf : (Function.mulSupport Hg).Finite := finite_mulSupport_htFin F g
  have hhf : (Function.mulSupport Hh).Finite := finite_mulSupport_htFin F h
  let Z : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i =>
    ((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i *
      (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ
  have hsup : ∀ i v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Z i p.1 p.2))) ≤
      Kx i v * (Hg v * Hh v) := fun i v => by
    refine Finset.sup_le fun p _ => (GlobalTheory.absFin_mul_mul_transpose_le g⁻¹ (Y i) h⁻¹ v p.1 p.2).trans ?_
    rw [GlobalTheory.MovedLat.htFin_bc_inv, GlobalTheory.MovedLat.htFin_bc_inv]
    calc _ ≤ Hg v * Kx i v * Hh v := mul_le_mul' (mul_le_mul' le_rfl (hKxb i v)) le_rfl
      _ = Kx i v * (Hg v * Hh v) := by ring
  have hloc1 : ∀ i j v, ‖evFin F v ((e (Z i)).1 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK1b j (Z i) v
    calc _ ≤ K1 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K1 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK1c v i j) le_rfl
  have hloc2 : ∀ i j v, ‖evFin F v ((e (Z i)).2 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK2b j (Z i) v
    calc _ ≤ K2 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K2 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK2c v i j) le_rfl
  let H : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => Kc v * (Hg v * Hh v)
  have hH1 : ∀ v, 1 ≤ H v := fun v =>
    one_le_mul_of_one_le_of_one_le (hKc1 v) (one_le_mul_of_one_le_of_one_le (one_le_htOf _ _) (one_le_htOf _ _))
  have hHf : (Function.mulSupport H).Finite :=
    (hKcf.union (hgf.union hhf)).subset ((Function.mulSupport_mul _ _).trans
      (Set.union_subset_union le_rfl (Function.mulSupport_mul _ _)))
  obtain ⟨M, hM0, hMb, hMv⟩ := GlobalTheory.SmoothForms.denom_global H hH1 hHf
  have hfin : ∀ x : AF F, (∀ v, ‖evFin F v x‖₊ ≤ H v) → GlobalTheory.FinSupp.FinDiv F N (((N * M : ℕ) : AF F) * x) := by
    intro x hx v
    refine ⟨(M : Fv F v) * evFin F v x, Valued.toNormedField.norm_le_one_iff.1 (hMv v _ (hx v)), ?_⟩
    rw [map_mul, map_natCast]
    push_cast
    ring
  refine ⟨N * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun i j => ⟨hfin _ (hloc1 i j), hfin _ (hloc2 i j)⟩⟩
  have hMH : (M : ℝ≥0) ≤ C0 * (heightGL F g * heightGL F h) := by
    refine hMb.trans (le_of_eq_of_le (finprod_mul_distrib hKcf ((hgf.union hhf).subset (Function.mulSupport_mul _ _))) ?_)
    refine mul_le_mul' le_rfl ?_
    rw [finprod_mul_distrib hgf hhf]
    exact mul_le_mul' (GlobalTheory.MovedLat.finprod_htFin_le g) (GlobalTheory.MovedLat.finprod_htFin_le h)
  have := NNReal.coe_le_coe.2 hMH
  push_cast at this ⊢
  rw [pow_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left this (by positivity)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BumpPts

theorem exists_finset_closure_eq_top {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(X, W), Subring.closure (Set.range (constFn p W) ∪ ↑s) = ⊤ := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  letI := (p.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Sp k, ⊤) Γ(X, W) := h
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := Γ(Sp k, ⊤)) (A := Γ(X, W))
  refine ⟨s, ?_⟩
  have e : Set.range (constFn p W) = Set.range (algebraMap Γ(Sp k, ⊤) Γ(X, W)) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b, ?_⟩
      have hb : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b) = b := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
      show (p.appLE ⊤ W (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b)) = _
      rw [hb]
      rfl
  rw [e, ← Algebra.adjoin_eq_ring_closure, hs]
  rfl

theorem exists_cInf_bump (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (hp : IsProjOver p) (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)) (hO : IsOpen O)
    (hy : y ∈ O) : ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧
      tsupport χ ⊆ O := by
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hp
  haveI : T2Space (CxPts p σ) := t2Space_cxPts_of_isProjOver σ hp
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top y.1)
  have hyW' : y ∈ ptsIn p σ W := hyW
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top p hW
  let φ : CxPts p σ → (s → ℂ) := fun z a => ev p σ W a.1 z

  obtain ⟨S, hS, hSO⟩ : ∃ S ∈ 𝓝 (φ y), ∀ z ∈ ptsIn p σ W, φ z ∈ S → z ∈ O := by
    let l := Filter.comap φ (𝓝 (φ y)) ⊓ 𝓟 (ptsIn p σ W)
    have hφl : Tendsto φ l (𝓝 (φ y)) := tendsto_comap.mono_left inf_le_left
    have ht : Tendsto (fun z => z) l (𝓝 y) := by
      refine (PtsOver.tendsto_iff_of_generators hW hyW hs).2 ⟨?_, fun f hf => ?_⟩
      · exact mem_inf_of_right (mem_principal_self _)
      · exact ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hφl
    have h : O ∈ l := ht (hO.mem_nhds hy)
    rw [mem_inf_principal] at h
    obtain ⟨S, hS, hSO⟩ := mem_comap.1 h
    exact ⟨S, hS, fun z hz hzS => hSO hzS hz⟩
  obtain ⟨F, hFS, hFc, hFd, hFr, hF1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hS
  let K : Set (CxPts p σ) := {z | z ∈ ptsIn p σ W ∧ φ z ∈ tsupport F}

  have hKc : IsCompact K := by
    refine isCompact_iff_ultrafilter_le_nhds.2 fun u hu => ?_
    have hKu : K ∈ u := le_principal_iff.1 hu
    have hWu : ∀ᶠ z in (u : Filter (CxPts p σ)), z ∈ ptsIn p σ W := mem_of_superset hKu fun z hz => hz.1
    obtain ⟨v, -, hv⟩ := hFc.ultrafilter_le_nhds (u.map φ)
      (le_principal_iff.2 (Ultrafilter.mem_map.2
        (mem_of_superset hKu fun z (hz : z ∈ K) => hz.2)))
    have hv' : Tendsto φ u (𝓝 v) := hv
    have hcst : ∀ a : k, ∀ z ∈ ptsIn p σ W, ev p σ W (constFn p W a) z = ev p σ W (constFn p W a) y :=
      fun a z hz => by
        show valR z.1 W _ = valR y.1 W _
        rw [valR_constFn p z.1 W hz, valR_constFn p y.1 W hyW, z.2, y.2]
    have hlim : ∀ f : Γ(X, W), ∃ c, Tendsto (fun z => ev p σ W f z) u (𝓝 c) := by
      intro f
      have hf : f ∈ Subring.closure (Set.range (constFn p W) ∪ ↑s) := hs ▸ Subring.mem_top f
      induction hf using Subring.closure_induction with
      | mem f hf =>
        rcases hf with ⟨a, rfl⟩ | hf
        · exact ⟨_, tendsto_const_nhds.congr' (hWu.mono fun z hz => (hcst a z hz).symm)⟩
        · exact ⟨v ⟨f, hf⟩, ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hv'⟩
      | zero =>
        exact ⟨0, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm)⟩
      | one =>
        exact ⟨1, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm)⟩
      | add f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c + d, (hc.add hd).congr fun z => (ev_add f g z).symm⟩
      | neg f _ hf =>
        obtain ⟨c, hc⟩ := hf
        exact ⟨-c, hc.neg.congr' (hWu.mono fun z hz => by
          show -ev p σ W f z = ev p σ W (-f) z
          rw [ev_eq hz, ev_eq hz, map_neg])⟩
      | mul f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c * d, (hc.mul hd).congr fun z => (ev_mul f g z).symm⟩
    choose c hc using hlim
    let ψ : Γ(X, W) →+* ℂ :=
      { toFun := c
        map_one' := tendsto_nhds_unique (hc 1)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm))
        map_mul' := fun f g => tendsto_nhds_unique (hc (f * g))
          (((hc f).mul (hc g)).congr fun z => (ev_mul f g z).symm)
        map_zero' := tendsto_nhds_unique (hc 0)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm))
        map_add' := fun f g => tendsto_nhds_unique (hc (f + g))
          (((hc f).add (hc g)).congr fun z => (ev_add f g z).symm) }
    have hψ : ∀ a, ψ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W a) = σ a := fun a => tendsto_nhds_unique (hc _)
      (tendsto_const_nhds.congr' (hWu.mono fun z hz => (ev_algX hz a).symm))
    let z' : CxPts p σ := ofHom hW ψ hψ
    have hz'W : z' ∈ ptsIn p σ W := ofHom_mem hW ψ hψ
    have hz'ev : ∀ f, ev p σ W f z' = c f := fun f => ev_ofHom hW ψ hψ f
    have ht : Tendsto (fun z => z) (u : Filter (CxPts p σ)) (𝓝 z') := by
      refine (PtsOver.tendsto_iff_of_generators hW hz'W hs).2 ⟨hWu, fun f _ => ?_⟩
      have := hc f
      rw [← hz'ev f] at this
      exact this
    have hφz' : φ z' = v := funext fun a =>
      (hz'ev a.1).trans (tendsto_nhds_unique (hc a.1) (((continuous_apply a).tendsto _).comp hv'))
    refine ⟨z', ⟨hz'W, ?_⟩, ht⟩
    rw [hφz']
    exact hFc.isClosed.mem_of_tendsto hv' (mem_of_superset hKu fun z hz => hz.2)
  have hKcl : IsClosed K := hKc.isClosed
  let χ : CxPts p σ → ℝ := (ptsIn p σ W).indicator fun z => F (φ z)
  have hsupp : Function.support χ ⊆ K := fun z hz => by
    rw [Function.mem_support, Set.indicator_apply_ne_zero] at hz
    exact ⟨hz.1, subset_tsupport _ hz.2⟩
  refine ⟨χ, fun z => ?_, fun z => Set.indicator_nonneg (fun w _ => (hFr ⟨_, rfl⟩).1) z, ?_, ?_⟩
  · by_cases hz : z ∈ ptsIn p σ W
    · refine ⟨W, s, inferInstance, fun a => a.1, F, Set.univ, hz, isOpen_univ, trivial,
        hFd.contDiffOn, ?_⟩
      filter_upwards [(isOpen_ptsIn W).mem_nhds hz] with w hw
      exact Set.indicator_of_mem hw _
    · have hzK : z ∉ K := fun h => hz h.1
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKcl.isOpen_compl.mem_nhds hzK] with w hw
      exact Function.notMem_support.1 fun h => hw (hsupp h)
  · show 0 < (ptsIn p σ W).indicator (fun z => F (φ z)) y
    rw [Set.indicator_of_mem hyW', hF1]
    exact one_pos
  · exact (closure_minimal hsupp hKcl).trans fun z hz => hSO z hz.1 (hFS hz.2)

end GlobalTheory.BumpPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTameCharactersSeriesIdempotentsTameLabelle
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TameTieOfGood

variable {D : D7}

theorem exists_div (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) : ∃ w, P.Div k w := by
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) (P.pb k).asIdeal (by
    have : RingHom.ker (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective _ _)
    rw [this]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, ?_⟩
  · rintro rfl
    apply (P.pb k).ne_bot
    rw [← hQ']
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  · exact HeightOneSpectrum.ext hQ'

theorem tameTie_of_given {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hG : Given R F) : GlobalTheory.DimPartsCompare.TameTie D R.C.W.om := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hL := hG.core.lev
  obtain ⟨L, h1, h2, h3⟩ := hG.types k
  refine ⟨L, h1, h2, fun v j => ?_⟩
  obtain ⟨PP, hPP⟩ := exists_div R.C.P k
  obtain ⟨u0, hu0, -⟩ := GlobalTheory.GLp.Model.exists_gen L
  have hp := D.host.g_prime k
  set a : ℕ := (u0 : ZMod (D.host.g k)).val with ha_def
  have haz : ((a : ℕ) : ZMod (D.host.g k)) = u0 := ZMod.natCast_zmod_val _
  have ha : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 := by
    rw [← hu0, ← haz, map_natCast]
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha, ← hu0]; simp
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro h; rw [h] at ha0; exact ha0 (by simp)
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have hgPP := Formalism.IndefR.Fin.g_mem_of_div R.C hPP
  have hk0 : IsUnit ((a : ℕ) : kP PP) := by
    have hc : IsCoprime ((a : ℕ) : kP PP) ((D.host.g k : ℕ) : kP PP) := by
      have := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (kP PP))
      simpa using this
    have hg0 : ((D.host.g k : ℕ) : kP PP) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hgPP
    rw [hg0] at hc
    exact isCoprime_zero_right.1 hc
  set u : (kP PP)ˣ := hk0.unit with hu_def
  have key := h3 v j PP hPP a u ha hk0.unit_spec
  have h2' := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3' := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu_def, hk0.unit_spec, map_natCast])
  rw [h2', MonoidHom.inv_apply, _root_.inv_inj] at h3'
  have hw : ZMod.unitOfCoprime a hcop = u0 := Units.ext (by rw [ZMod.coe_unitOfCoprime, haz])
  have hχ : (R.chi ((j : ℕ) + 1) PP u : ℂˣ) = GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.chiTame R.C.W.om k j u0 := by
    rw [h3', ← hw]; rfl
  have hgen : ∀ w : (ZMod (D.host.g k))ˣ, algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) w = L.gen 1 → w = u0 :=
    fun w hw' => Units.ext ((algebraMap _ _).injective (hw'.trans hu0.symm))
  rcases key with e | e
  · refine ⟨_, Or.inl rfl, fun b => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab L ⟨(D.nd.chiT k v j).ne_zero, fun w hw' => ?_⟩ b⟩
    rw [hgen w hw', e, hχ]
  · refine ⟨_, Or.inr rfl, fun b => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab L ⟨(D.nd.chiT k v j).ne_zero, fun w hw' => ?_⟩ b⟩
    rw [hgen w hw', e, hχ, MonoidHom.inv_apply]

theorem exists_tameTie_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∃ om, GlobalTheory.DimPartsCompare.TameTie D om :=
  fun R F hG => ⟨_, tameTie_of_given R F hG⟩

end GlobalTheory.TameTieOfGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleLevelComponentEqOfCardTorsion
section
set_option autoImplicit false

open GlobalTheory.HTLat

namespace GlobalTheory

theorem exists_pow_prime_root_of_card_torsion {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    {c : ℕ} (hcard : ∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) (k : ℕ) (y : M)
    (hy : y ^ (l ^ k) = 1) : ∃ z : M, z ^ (l ^ (k + 1)) = 1 ∧ z ^ l = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let T : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n)).ker
  have hT : ∀ n, Nat.card (T n) = l ^ (c * n) := fun n => by
    rw [← hcard n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [T, MonoidHom.mem_ker])
  let φ : T (k + 1) →* M := (powMonoidHom l).comp (T (k + 1)).subtype
  have hker : Nat.card φ.ker = l ^ c := by
    rw [← mul_one c, ← hT 1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := y.2
      simp only [T, φ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        powMonoidHom_apply, Subgroup.coe_subtype] at this
      simpa [T, MonoidHom.mem_ker] using this
    · have hz : (z : M) ^ l = 1 := by simpa [T] using MonoidHom.mem_ker.1 z.2
      simp only [T, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [pow_succ' l k, pow_mul, hz, one_pow]
    · have := z.2
      simpa [T, φ, MonoidHom.mem_ker] using this
  have hrange : Nat.card φ.range = l ^ (c * k) := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker, hT (k + 1), mul_add, mul_one, pow_add, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hl c) h1
  have hfin : Finite (T k) := Nat.finite_of_card_ne_zero (by rw [hT k]; exact (pow_pos hl _).ne')
  have hle : φ.range ≤ T k := by
    rintro _ ⟨z, rfl⟩
    have := z.2
    simp only [T, MonoidHom.mem_ker, powMonoidHom_apply] at this ⊢
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
      Subgroup.coe_subtype]
    rw [← pow_mul, ← pow_succ', this]
  have heq : φ.range = T k := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hT k])
  have hyT : y ∈ T k := by simpa [T, MonoidHom.mem_ker] using hy
  rw [← heq] at hyT
  obtain ⟨z, hz⟩ := hyT
  exact ⟨z.1, MonoidHom.mem_ker.1 z.2, hz⟩

theorem exists_tate_lev_eq_of_card_torsion :
    ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ),
      (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) →
      ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  intro M _ l _ c hcard N x hx
  have h := exists_pow_prime_root_of_card_torsion hcard
  choose r hr1 hr2 using h
  let g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1} := fun n =>
    Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n
  have hg0 : (g 0).1 = x := rfl
  have hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1 := fun n => hr2 (N + n) (g n).1 (g n).2
  have hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1 := fun n k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_mul]
      show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _
      rw [hgs, ih]
  let s : ℕ → M := fun n => (g n).1 ^ (l ^ N)
  have hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n := fun n => by
    refine ⟨?_, ?_⟩
    · simp only [s]
      rw [← pow_mul, ← pow_add, (g n).2]
    · simp only [s]
      rw [← pow_mul, mul_comm, pow_mul, hgs]
  refine ⟨Tate.mk s hs, ?_⟩
  rw [Tate.lev_mk]
  simp only [s]
  have := hgk 0 N
  rw [zero_add] at this
  rw [this, hg0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.PullFactor

theorem objMap_factor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₀ S₁ T : Scheme.{0}) (s₀ : S₀ ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (t : T ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o : GlobalTheory.UPel.HT.Obj b N t) (g : S₁ ⟶ S₀) (h : T ⟶ S₁), GlobalTheory.UPel.HT.ObjMap o₁ o₀ g → GlobalTheory.UPel.HT.ObjMap o o₀ (h ≫ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o o₁ h) := by
  intro p _ D R _ b N S₀ S₁ T s₀ s₁ t o₀ o₁ o g h m₁ m
  exact GlobalTheory.UPel.HT.MapComp.cancel m m₁

end GlobalTheory.UPel.HT.PullFactor
end

