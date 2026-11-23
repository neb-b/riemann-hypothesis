module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.BasicNotions MvPolynomial
open scoped Matrix

namespace GlobalTheory.NabBC

variable {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K]

theorem mem_localization_of_mem' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L : Submodule R W} {x : W} (h : x ∈ L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L :=
  show ∃ s ∈ p.primeCompl, s • x ∈ L from ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact h⟩

abbrev vmap {n : ℕ} (f : K₀ →+* K) (x : Fin n → K₀) : Fin n → K := fun a => f (x a)

theorem vmap_add {n : ℕ} (f : K₀ →+* K) (x y : Fin n → K₀) : vmap f (x + y) = vmap f x + vmap f y := by
  funext a; simp [vmap]

theorem vmap_smul {n : ℕ} (f : K₀ →+* K) (r : 𝓞 K₀) (x : Fin n → K₀) :
    vmap f (r • x) = RingOfIntegers.mapRingHom f r • vmap f x := by
  funext a
  change f ((r : K₀) * x a) = ((RingOfIntegers.mapRingHom f r : 𝓞 K) : K) * f (x a)
  rw [map_mul]
  rfl

theorem span_image_span {n : ℕ} (f : K₀ →+* K) (S : Set (Fin n → K₀)) :
    Submodule.span (𝓞 K) (vmap f '' (Submodule.span (𝓞 K₀) S : Set (Fin n → K₀))) =
      Submodule.span (𝓞 K) (vmap f '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      have : vmap f (0 : Fin n → K₀) = 0 := by funext a; simp [vmap]
      rw [this]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [vmap_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [vmap_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem localization_span_image_le {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {A B : Submodule (𝓞 K₀) (Fin n → K₀)} (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀)))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
  have key : Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨t, ht, hta⟩ := h ha
    exact show ∃ s ∈ w.asIdeal.primeCompl, s • vmap f a ∈ _ from
      ⟨RingOfIntegers.mapRingHom f t, hw t ht, by rw [← vmap_smul]; exact Submodule.subset_span ⟨_, hta, rfl⟩⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := key hsx
  exact show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ _ from
    ⟨t * s, Submonoid.mul_mem _ ht hs, by rw [mul_smul]; exact htx⟩

theorem span_vmap_colLat {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    Submodule.span (𝓞 K) (vmap f '' (colLat C : Set (Fin n → K₀))) = colLat (Formalism.UG.bc f C) := by
  unfold colLat
  rw [span_image_span, ← Set.range_comp]
  congr 1

theorem isBasisAt_span_vmap {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {L : Submodule (𝓞 K₀) (Fin n → K₀)} {C : GL (Fin n) K₀} (hC : IsBasisAt w₀ L C) :
    IsBasisAt w (Submodule.span (𝓞 K) (vmap f '' (L : Set (Fin n → K₀)))) (Formalism.UG.bc f C) := by
  unfold IsBasisAt at hC ⊢
  rw [← span_vmap_colLat]
  have h1 : L ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (colLat C) := hC ▸ fun x hx => mem_localization_of_mem' _ hx
  have h2 : colLat C ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal L := hC.symm ▸ fun x hx => mem_localization_of_mem' _ hx
  exact le_antisymm (localization_span_image_le f w₀ w hw h1) (localization_span_image_le f w₀ w hw h2)

theorem tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K) (emb : ι → E →+* K₀) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) :
    tauLat (fun τ => f.comp (emb τ)) τ M = Submodule.span (𝓞 K) (vmap f '' (tauLat emb τ M : Set (Fin n → K₀))) := by
  unfold tauLat
  rw [span_image_span, Set.image_image]
  rfl

theorem invTr_bc {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    inside₂ K n (Formalism.UG.bc f C) = Formalism.UG.bc f (inside₂ K₀ n C) := by
  apply Units.ext
  change (((Formalism.UG.bc f C)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
    ((Formalism.UG.bc f (inside₂ K₀ n C) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [← map_inv, bc_coe, bc_coe, ← Matrix.transpose_map]
  rfl

theorem isBasisAt_dualFr_tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (τ : ι) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    (C : GL (Fin n) K₀) (hC : IsBasisAt w₀ (tauLat emb τ M) C) :
    IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (inside₂ K₀ n C)) := by
  rw [← invTr_bc]
  refine GlobalTheory.DualWeylDual.isBasisAt_dualFr w (tauLatLattice E K ι n _ τ M hM).fg ?_
  rw [tauLat_comp]
  exact isBasisAt_span_vmap f w₀ w hw hC

theorem nabStd_le_span_map {ι : Type} [Fintype ι] {n : ℕ} (f : K₀ →+* K) (lam : ι → DomWeight n) :
    nabStd K lam ≤ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) := by
  have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
  have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
  rw [h1, ← h2]
  intro x hx
  exact Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩

theorem map_smul_int {σ : Type} (f : K₀ →+* K) (t : 𝓞 K₀) (P : MvPolynomial σ K₀) :
    RingOfIntegers.mapRingHom f t • MvPolynomial.map f P = MvPolynomial.map f (t • P) := by
  ext m
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
  change ((RingOfIntegers.mapRingHom f t : 𝓞 K) : K) * f (P.coeff m) = f ((t : K₀) * P.coeff m)
  rw [map_mul]
  rfl

theorem mem_localization_span_map {E ι : Type} [Field E] [NumberField E] [Fintype ι] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M)
    (w : HeightOneSpectrum (𝓞 K)) {F : Pol K ι n}
    (hF : F ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :
    F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)))) := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsFullLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  set N' := Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) with hN'
  have key : ∀ H ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))),
      actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) H ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' := by
    intro H hH
    refine (Submodule.span_le (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N').comap
      ((actP lam (fun τ => Formalism.UG.bc f (B₀ τ))).restrictScalars (𝓞 K)))).2 ?_ hH
    rintro _ ⟨g, hg, rfl⟩
    show actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N'
    rw [← GlobalTheory.ValCmp.use₂]
    have hg' : actP lam B₀ g ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) := by
      rw [L0]
      exact Submodule.mem_map_of_mem (mem_localization_of_mem' _ hg)
    obtain ⟨t, ht, htg⟩ := hg'
    refine ⟨RingOfIntegers.mapRingHom f t, hw t ht, ?_⟩
    have e := map_smul_int f t (actP lam B₀ g)
    refine (congrArg (· ∈ N') e).mpr ?_
    exact Submodule.subset_span ⟨_, htg, rfl⟩
  have hF' : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :=
    mem_localization_of_mem' _ hF
  rw [L1] at hF'
  obtain ⟨G, ⟨s, hs, hsG⟩, rfl⟩ := hF'
  obtain ⟨t, ht, htG⟩ := key _ (nabStd_le_span_map f lam hsG)
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  convert htG using 1
  rw [mul_smul]
  congr 1
  exact (((actP lam fun τ => Formalism.UG.bc f (B₀ τ)).restrictScalars (𝓞 K)).map_smul s G).symm

theorem nabBaseChange : ∀ (E K₀ K ι : Type) [Field E] [NumberField E] [Field K₀] [NumberField K₀]
    [Field K] [NumberField K] [Fintype ι] (n : ℕ) (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E M →
    nabAtr (fun τ => f.comp (emb τ)) lam M ≤
      Submodule.span (𝓞 K) {y : VV K lam | ∃ x ∈ nabAtr emb lam M,
        (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} := by
  intro E K₀ K ι _ _ _ _ _ _ _ n f emb lam M hM F hF
  obtain ⟨-, -, hV⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hP : (F : Pol K ι n) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) :=
    GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => GlobalTheory.NabBC.mem_localization_span_map f emb lam M hM w hF
  have hS : ((VV K lam).subtype.restrictScalars (𝓞 K)) ''
      {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} =
      MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)) := by
    ext P
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
      exact ⟨x.1, hx, hxy.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hxV : x ∈ VV K₀ lam := hV K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) x hx
      exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam x hxV⟩, ⟨⟨x, hxV⟩, hx, rfl⟩, rfl⟩
  rw [← hS, ← Submodule.map_span] at hP
  obtain ⟨y, hy, hyF⟩ := hP
  have e : y = F := Subtype.ext hyF
  rwa [← e]

end GlobalTheory.NabBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X) (n : ℕ) (z : X) :
    (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (a c : ℚ) (D : X → ℚ), 0 ≤ c → QNum p N a D → QNum p N (c * a) (c • D) := by
  intro X _ _ p hp N a c D hc hD
  letI := algebraΓOfHom p
  obtain ⟨m, D₀, hm, hE, rfl, hI⟩ := hD
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v : ℕ, 0 < v ∧ c = (u : ℚ) / v := by
    refine ⟨c.num.toNat, c.den, c.den_pos, ?_⟩
    have h0 : ((c.num.toNat : ℕ) : ℤ) = c.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)
    have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    rw [eq_div_iff hd, Rat.mul_den_eq_num]
    exact_mod_cast h0.symm
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨v * m, u • D₀, Nat.mul_pos hv hm, eff_nsmul' hE u, ?_, fun C hC => ?_⟩
  · funext z
    simp only [qWeil, Pi.smul_apply, smul_eq_mul, mult_nsmul']
    push_cast
    field_simp
  · have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB (u • D₀)) (toLB D₀) (toLB D₀)
      (isLB_toLB _) (isLB_toLB _) (isLB_toLB _) u 0 C hC
      (by rw [← toPic_apply, ← toPic_apply, map_nsmul, zero_nsmul, add_zero])
    rw [e, Nat.cast_zero, zero_mul, add_zero]
    have h1 := hI C hC
    push_cast
    rw [mul_assoc, ← h1]
    field_simp

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfGermEqZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.Vanishing.ProdNe

theorem eq_zero_of_germ_eq_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    {p : Y ⟶ Sp k} {B : LB Y} (hc : ∀ z : Y, ∃ j, z ∈ B.U j) (f : H0 p B ⊤) (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) (h0 : H0.germ i y (show y ∈ (⊤ : Y.Opens) from trivial) hi f = 0) : f = 0 := by
  have hi0 : f.loc i = 0 := by
    apply germ_injective_of_isIntegral Y y (memInf (U := ⊤) trivial hi)
    rw [map_zero]
    exact h0
  refine H0.ext_germ fun z hz => ?_
  obtain ⟨j, hj⟩ := hc z
  refine ⟨j, hj, ?_⟩
  have hj0 : f.loc j = 0 := by
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (B.U i).isOpen (B.U j).isOpen ⟨y, hi⟩ ⟨z, hj⟩
    apply germ_injective_of_isIntegral Y w (memInf (U := ⊤) trivial hwj)
    rw [map_zero]
    have e := H0.germ_change (O := ⊤) i j w (show w ∈ (⊤ : Y.Opens) from trivial) hwi hwj f
    have e2 : H0.germ (O := ⊤) i w (show w ∈ (⊤ : Y.Opens) from trivial) hwi f = 0 := by
      rw [H0.germ_apply, hi0, map_zero]
    rw [e2] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h
  rw [H0.germ_apply, hj0, map_zero, map_zero]

theorem mul_ne_zero : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {P B N : LB Y} (C : ProdChart P B N) (σ : H0 p P ⊤) (f : H0 p B ⊤), σ ≠ 0 → f ≠ 0 → C.mul σ f ≠ 0 := by
  intro k _ Y _ p P B N C σ f hσ hf hmul
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨t, ha, hb, hc⟩ := C.cover y
  have e := C.germ_mul σ f t y trivial ha hb hc
  rw [hmul, map_zero] at e
  rcases mul_eq_zero.mp e.symm with h | h
  · exact hσ (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.a t, h.1⟩) σ y _ ha h)
  · exact hf (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.b t, h.2.1⟩) f y _ hb h)

end GlobalTheory.Vanishing.ProdNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatUnitProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)

def IsBddUnit (G : WTZ E) (s t : Rul Xo c) : Prop :=
  Even G.2 ∧ s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw G) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw G) ∧
    GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧
    (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z,
      GlobalTheory.AllWt.homN (U σ) x G s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) x (-G) t z ≤ C) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)

theorem exZ_zero' : Formalism.L2.Pj.exZ Dw (0 : WTZ E) = 0 := by
  funext i; cases i <;> rfl

theorem exZ_add_eq' (G G' : WTZ E) : Formalism.L2.Pj.exZ Dw (G + G') = Formalism.L2.Pj.exZ Dw G + Formalism.L2.Pj.exZ Dw G' :=
  funext fun i => exZ_add _ _ i

theorem exZ_neg_eq' (G : WTZ E) : Formalism.L2.Pj.exZ Dw (-G) = -Formalism.L2.Pj.exZ Dw G := by
  funext i; cases i <;> rfl

theorem homN_idem_le {σ : c.F →+* ℂ} (V : Unf Xo c σ r) {z} (hz : z ∈ framesOn V Z) :
    GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z ≤ 1 := by
  obtain ⟨hd, hl⟩ := hz
  rcases eq_or_ne (GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z) 0 with h | h
  · rw [h]; exact zero_le_one
  · rw [GlobalTheory.FlatLine.homN_idem V x hd hl (GlobalTheory.FlatLine.tested_of_homN_ne V x hd h)]

theorem isBddUnit_zero : IsBddUnit U x Z 0 (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z) := by
  have hm : GlobalTheory.FlatLine.idem Z ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (0 : WTZ E)) := by
    rw [exZ_zero']; exact GlobalTheory.FlatLine.idem_mem_secZ Z
  refine ⟨by simp, hm, by rwa [exZ_zero', neg_zero, ← exZ_zero' (Dw := Dw)], GlobalTheory.FlatLine.idem_mul_idem Z,
    GlobalTheory.FlatLine.idem_mul_idem Z, GlobalTheory.FlatLine.idem_mul_idem Z, fun σ _ => ⟨1, fun z hz => ?_⟩, 1, one_pos,
    fun la v hv => ?_⟩
  · rw [neg_zero]; exact ⟨homN_idem_le x Z (U σ) hz, homN_idem_le x Z (U σ) hz⟩
  · rw [Nat.cast_one, one_smul, GlobalTheory.FlatLine.val_idem hv]; exact ⟨le_rfl, le_rfl⟩

variable {U x Z}

theorem IsBddUnit.mul {G G' : WTZ E} {s t s' t' : Rul Xo c} (h : IsBddUnit U x Z G s t)
    (h' : IsBddUnit U x Z G' s' t') : IsBddUnit U x Z (G + G') (s * s') (t * t') := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  obtain ⟨hG', hs', ht', his', hit', hst', hb', m', hm', hv'⟩ := h'
  refine ⟨hG.add hG', ?_, ?_, by rw [← mul_assoc, his], by rw [← mul_assoc, hit], ?_,
    fun σ hσ => ?_, m * m', Nat.mul_pos hm hm', fun la v hw => ?_⟩
  · rw [exZ_add_eq']; exact GlobalTheory.AllWt.mul_mem_secZ hs hs'
  · rw [exZ_add_eq', neg_add]; exact GlobalTheory.AllWt.mul_mem_secZ ht ht'
  · rw [mul_mul_mul_comm, hst, hst', GlobalTheory.FlatLine.idem_mul_idem]
  · obtain ⟨C, hC⟩ := hb σ hσ
    obtain ⟨C', hC'⟩ := hb' σ hσ
    refine ⟨max C 0 * max C' 0, fun z hz => ⟨?_, ?_⟩⟩
    · rw [GlobalTheory.AllWt.homN_mul (U σ) x hG hG' s s' z hz.1]
      exact mul_le_mul ((hC z hz).1.trans (le_max_left _ _)) ((hC' z hz).1.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
    · rw [neg_add, GlobalTheory.AllWt.homN_mul (U σ) x (G := -G) (G' := -G') hG.neg hG'.neg t t' z hz.1]
      exact mul_le_mul ((hC z hz).2.trans (le_max_left _ _)) ((hC' z hz).2.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
  · have hV := GlobalTheory.FlatLine.isVal_valOn hw
    rw [Nat.cast_mul, ← smul_mul_smul_comm, ← smul_mul_smul_comm, hV.mul, hV.mul]
    exact ⟨add_nonneg (hv la v hw).1 (hv' la v hw).1, add_nonneg (hv la v hw).2 (hv' la v hw).2⟩

theorem IsBddUnit.swap {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) : IsBddUnit U x Z (-G) t s := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  refine ⟨hG.neg, by rwa [exZ_neg_eq'], by rwa [exZ_neg_eq', neg_neg], hit, his,
    by rw [mul_comm, hst], fun σ hσ => ?_, m, hm, fun la v hw => (hv la v hw).symm⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  exact ⟨C, fun z hz => ⟨(hC z hz).2, by rw [neg_neg]; exact (hC z hz).1⟩⟩

theorem exists_nsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (k : ℕ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (k • G) s' t' := by
  induction k with
  | zero => exact ⟨_, _, by rw [zero_nsmul]; exact isBddUnit_zero U x Z⟩
  | succ k ih =>
    obtain ⟨s', t', h'⟩ := ih
    exact ⟨_, _, by rw [succ_nsmul]; exact h'.mul h⟩

theorem exists_zsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (n : ℤ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (n • G) s' t' := by
  cases n with
  | ofNat k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h k
    exact ⟨s', t', by rw [Int.ofNat_eq_natCast, natCast_zsmul]; exact h'⟩
  | negSucc k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h (k + 1)
    exact ⟨t', s', by rw [negSucc_zsmul]; exact h'.swap⟩

theorem exists_sum {ι : Type} (G : ι → WTZ E) (hu : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t)
    (n : ι → ℤ) (S : Finset ι) : ∃ s t : Rul Xo c, IsBddUnit U x Z (∑ i ∈ S, n i • G i) s t := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨_, _, by rw [Finset.sum_empty]; exact isBddUnit_zero U x Z⟩
  | insert a S ha ih =>
    obtain ⟨s, t, h⟩ := ih
    obtain ⟨s₀, t₀, h₀⟩ := hu a
    obtain ⟨s₁, t₁, h₁⟩ := exists_zsmul h₀ (n a)
    exact ⟨_, _, by rw [Finset.sum_insert ha]; exact h₁.mul h⟩

end GlobalTheory.FlatUnitProd


open GlobalTheory.FlatUnitProd in
theorem GlobalTheory.FlatUnitProd.exists_unit_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ι : Type) [Fintype ι] (G : ι → WTZ E), (∀ i, Even (G i).2) → (∀ i, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)) → ∀ n : ι → ℤ, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (∑ i, n i • G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(∑ i, n i • G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t) := by
  intro E _ _ _ H Dw l Xo c r U x Z ι _ G hev hu n
  have hu' : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t := fun i => by
    obtain ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩ := hu i
    exact ⟨s, t, hev i, h1, h2, h3, h4, h5, h6, m, hm, hv⟩
  obtain ⟨s, t, -, h1, h2, h3, h4, h5, h6, m, hm, hv⟩ := exists_sum G hu' n Finset.univ
  exact ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (a b : ℕ), IsNef k N → IsBig k N → IsNef k N' → 0 < a → ∃ (N₀ : LB X) (h₀ : N₀.IsLB), cls N₀ h₀ = a • cls N hN + b • cls N' hN' ∧ IsNef k N₀ ∧ IsBig k N₀ := by
  first | exact @GlobalTheory.nef_big_of_cls_eq_smul_add_smul | exact GlobalTheory.nef_big_of_cls_eq_smul_add_smul | (intros; apply GlobalTheory.nef_big_of_cls_eq_smul_add_smul <;> assumption)
end

