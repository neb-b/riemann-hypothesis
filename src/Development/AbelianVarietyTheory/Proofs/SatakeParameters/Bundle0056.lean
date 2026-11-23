module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSimpleRingOfCentralIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapFCoe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnrami
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_over : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL),
    K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  intro l _ P K LL W hK a
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro x
    exact ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨(W.emb a).comp e.symm.toAlgHom, ?_, ?_⟩
  · show ((W.emb a).comp e.symm.toAlgHom).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a
    ext x
    have : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) x) = x := e.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) this
  · intro τ hτ
    have hτ' : τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a := hτ
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    have h1 : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) y) = y := e.symm_apply_apply y
    have h2 := congrArg (fun f => f y) hτ'
    simp only [AlgHom.comp_apply] at h2 ⊢
    rw [h2]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) h1.symm

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

theorem exists_mem_one_sub_loc_dvd {R : Type} [CommRing R] [IsDedekindDomain R] (S : Finset (HeightOneSpectrum R))
    (I : Ideal R) (hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal) (c : R) [Finite (R ⧸ Ideal.span {c})] :
    ∃ s ∈ I, ∃ t r : R, (∀ P ∈ S, t ∉ P.asIdeal) ∧ t * (1 - s) = c * r := by
  have h1 : I ⊔ (⨅ P ∈ S, P.asIdeal) = ⊤ := by
    refine Ideal.sup_iInf_eq_top fun P hP => ?_
    obtain ⟨s, hs, hsP⟩ := hI P hP
    by_contra hne
    have := P.isMaximal.eq_of_le hne le_sup_right
    exact hsP (this ▸ (le_sup_left : I ≤ I ⊔ P.asIdeal) hs)
  have h2 : (1 : R) ∈ I ⊔ (⨅ P ∈ S, P.asIdeal) := h1 ▸ Submodule.mem_top
  obtain ⟨s0, hs0, π, hπ, hsum⟩ := Submodule.mem_sup.1 h2
  have hπ' : ∀ P ∈ S, π ∈ P.asIdeal := by
    intro P hP
    exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hπ P) hP
  have key : ∃ i j : ℕ, i < j ∧ Ideal.Quotient.mk (Ideal.span {c}) (π ^ i) = Ideal.Quotient.mk (Ideal.span {c}) (π ^ j) := by
    obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun i : ℕ => Ideal.Quotient.mk (Ideal.span {c}) (π ^ i))
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact ⟨i, j, h', h⟩
    · exact ⟨j, i, h', h.symm⟩
  obtain ⟨i, j, hij, h⟩ := key
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨1 - π ^ i, ?_, 1 - π ^ (d + 1), r, ?_, ?_⟩
  · have : (1 - π) ∣ 1 - π ^ i := by simpa using sub_dvd_pow_sub_pow (1 : R) π i
    obtain ⟨u, hu⟩ := this
    have hs : 1 - π = s0 := by rw [← hsum]; ring
    rw [hu, hs]
    exact I.mul_mem_right _ hs0
  · intro P hP hmem
    have : π ^ (d + 1) ∈ P.asIdeal := P.asIdeal.pow_mem_of_mem (hπ' P hP) _ (Nat.succ_pos d)
    have h1 : (1 : R) ∈ P.asIdeal := by simpa using P.asIdeal.add_mem hmem this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rw [← hr]; ring

theorem finite_divLat_quot_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA cB : ℕ), Submodule.IsFullLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < cB → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) := by
  intro E _ _ _ a b S N N' cA cB hN hN' hA hB
  classical
  obtain ⟨G, hG⟩ := hN.fg
  have hA' : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (cB : E) ≠ 0 := by exact_mod_cast hB.ne'
  have memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  have memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔
      ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x := fun x => Iff.rfl
  have memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  let ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b) :=
    { toFun := fun x g => (cA : 𝓞 E) • x g
      map_add' := by intro x y; funext g; simp
      map_smul' := by intro r x; funext g; simp [smul_comm r] }
  have ev_inj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hsp : Submodule.span E (G : Set (Sp E a)) = ⊤ := by
      rw [← hN.span_eq_top, ← hG, Submodule.span_span_of_tower]
    refine LinearMap.ext_on hsp fun g hg => ?_
    have := congrFun hx ⟨g, hg⟩
    have h2 : (cA : E) • x g = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact this
    simpa [hA'] using (smul_eq_zero.1 h2).resolve_left hA'
  let T : Submodule (𝓞 E) (G → Sp E b) := Submodule.pi Set.univ fun _ => N'
  have hT : T.FG := Submodule.fg_pi fun _ => hN'.fg
  let Z : Submodule (𝓞 E) (HomE E a b) := T.comap ev
  have memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N' := fun x =>
    ⟨fun h g => h g trivial, fun h g _ => h g⟩
  have hZ : Z.FG := by
    have : Module.Finite (𝓞 E) T := Module.Finite.iff_fg.2 hT
    have : Module.Finite (𝓞 E) Z := Module.Finite.of_injective (ev.restrict (p := Z) (q := T) fun x hx => hx) (by
      intro x y hxy
      exact Subtype.ext (ev_inj (congrArg Subtype.val hxy)))
    exact Module.Finite.iff_fg.1 this
  have hZD : Z ≤ divLat cA (homAt S N N') := by
    intro x hx
    rw [memD]
    intro P hP y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
    have : ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N' := by
      intro w hw
      rw [← hG] at hw
      induction hw using Submodule.span_induction with
      | mem g hg => exact (memZ x).1 hx ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add (f := _), smul_add]; exact N'.add_mem hu hv
      | smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]; exact N'.smul_mem r hu
    refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
    have h := this _ hsy
    rwa [LinearMap.map_smul_of_tower, smul_comm] at h
  have : Module.Finite (𝓞 E) Z := Module.Finite.iff_fg.2 hZ
  have hc : ((cB : 𝓞 E) * cA) ≠ 0 := by
    have : cB * cA ≠ 0 := by positivity
    exact_mod_cast this
  have : Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)
  have hsurj : Function.Surjective
      (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let I : Ideal (𝓞 E) := Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
    have hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal := by
      intro P hP
      have h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N' := fun g =>
        (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))
      choose f hf hf' using h1
      refine ⟨∏ g, f g, ?_, ?_⟩
      · show (∏ g, f g) • x ∈ Z
        rw [memZ]
        intro g
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]
        exact N'.smul_mem _ (hf' g)
      · intro h
        have := P.isPrime
        obtain ⟨g, _, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
        exact hf g hg
    obtain ⟨s, hs, t, r, ht, htr⟩ := exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)
    refine ⟨⟨s • x, hs⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show x - s • x ∈ mulLat cB (homAt S N N')
    have hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W),
        (cB : 𝓞 E) • (cB : E)⁻¹ • w = w := by
      intro W _ _ _ w
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩
    rw [memH]
    intro P hP y hy
    obtain ⟨u, hu, huy⟩ := (mem_locP P N' _).1 ((memD x).1 hx P hP y hy)
    refine (mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩
    have e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y := by
      have e2 : (x - s • x) y = (1 - s) • x y := by simp [sub_smul]
      rw [LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]
    rw [mul_smul, e1, smul_comm]
    exact N'.smul_mem r huy
  have := Module.Finite.of_surjective _ hsurj
  have : Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
    Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
  rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')
  rw [memM]
  exact ⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenMDetNeZeroOfNontrivial
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem jacobi_blocks_of_mul {R : Type} [CommRing R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (M Y : Matrix (α ⊕ β) (α ⊕ β) R) (d : R) (h : M * Y = d • (1 : Matrix (α ⊕ β) (α ⊕ β) R)) :
    M.toBlocks₁₁.det * Y.det = d ^ Fintype.card α * Y.toBlocks₂₂.det := by
  have hY : Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Y).symm
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks M).symm
  have h' := h
  rw [hM, hY, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero] at h'
  obtain ⟨h11, h12, -, -⟩ := Matrix.fromBlocks_inj.mp h'
  have key : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 1 * Y =
      Matrix.fromBlocks (d • 1) 0 Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    conv_lhs => rw [hY]
    rw [Matrix.fromBlocks_multiply, h11, h12]
    simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
    Matrix.det_smul, Matrix.det_one, mul_one] at hd
  exact hd

theorem genM_det_ne_zero_of_nontrivial (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  have hm : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [RingHom.map_det, hm, Matrix.det_one, map_zero] at h1
  exact one_ne_zero h1

theorem exists_equiv_castLE_rev {n s : ℕ} (hs : s ≤ n) : ∃ e : Fin (n - s) ⊕ Fin s ≃ Fin n,
    (∀ a, e (.inl a) = Fin.castLE (Nat.sub_le n s) a) ∧ ∀ q, e (.inr q) = Fin.rev (Fin.castLE hs q) := by
  refine ⟨(Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans
    (finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hs))), ?_, ?_⟩
  · intro a
    ext
    simp
  · intro q
    have hq := q.isLt
    ext
    simp
    omega

theorem jacobi_adjugate_perm {R : Type} [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (h1 : 1 ≤ s)
    (M : Matrix (Fin n) (Fin n) R) (hM : M.det ≠ 0) (σ : Equiv.Perm (Fin n)) : ∃ ε : ℤˣ,
    (Matrix.of fun q p : Fin s => M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det =
      (ε : ℤ) • (M.det ^ (s - 1) * (Matrix.of fun a b : Fin (n - s) =>
        M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det) := by
  obtain ⟨e, he1, he2⟩ := exists_equiv_castLE_rev hs
  obtain ⟨f, hf1, hf2⟩ : ∃ f : Fin (n - s) ⊕ Fin s ≃ Fin n,
      (∀ a, f (.inl a) = σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) ∧ ∀ p, f (.inr p) = σ (Fin.castLE hs p) :=
    ⟨(e.trans Fin.revPerm).trans σ, fun a => by simp [he1], fun p => by simp [he2]⟩
  have hmul : M.submatrix f e * M.adjugate.submatrix e f =
      M.det • (1 : Matrix (Fin (n - s) ⊕ Fin s) (Fin (n - s) ⊕ Fin s) R) := by
    rw [← Matrix.submatrix_mul M M.adjugate f e f e.bijective, Matrix.mul_adjugate]
    ext i j
    simp [Matrix.one_apply]
  have hJ := jacobi_blocks_of_mul _ _ _ hmul
  have hC : (M.submatrix f e).toBlocks₁₁ = Matrix.of fun a b : Fin (n - s) =>
      M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hf1, he1]
  have hT : (M.adjugate.submatrix e f).toBlocks₂₂ = Matrix.of fun q p : Fin s =>
      M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p)) := by
    ext q p
    simp [Matrix.toBlocks₂₂, hf2, he2]
  have hY : (M.adjugate.submatrix e f).det =
      ((Equiv.Perm.sign (e.trans f.symm) : ℤ) : R) * M.det ^ (n - 1) := by
    have hre : M.adjugate.submatrix e f = (M.adjugate.submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j
      simp
    rw [hre, Matrix.det_permute, Matrix.det_submatrix_equiv_self, Matrix.det_adjugate, Fintype.card_fin]
  rw [hC, hT, hY, Fintype.card_fin] at hJ
  have hpow : M.det ^ (n - 1) = M.det ^ (n - s) * M.det ^ (s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hJ
  refine ⟨Equiv.Perm.sign (e.trans f.symm), ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (n - s) hM)
  rw [zsmul_eq_mul]
  linear_combination -hJ

theorem cofAct_initMinor : ∀ (R : Type) [CommRing R] [IsDomain R] (n s : ℕ) (hs : s ≤ n), 1 ≤ s → ∀ σ : Equiv.Perm (Fin n), ∃ ε : ℤˣ, cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) = (ε : ℤ) • ((genM R n).det ^ (s - 1) * initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s)) := by
  intro R _ _ n s hs h1 σ
  obtain ⟨ε, hε⟩ := jacobi_adjugate_perm hs h1 (genM R n) (genM_det_ne_zero_of_nontrivial R n) σ
  refine ⟨ε, ?_⟩
  have hlhs : cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) =
      (Matrix.of fun q p : Fin s => (genM R n).adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
    rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext q p
    simp [cofAct]
  have hrhs : (Matrix.of fun a b : Fin (n - s) =>
      genM R n (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det =
      initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s) := by
    rw [initMinor]
    congr 1
  rw [hlhs, hε, hrhs]

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimes
section
namespace GlobalTheory.UPel.HT.Gen.SplitAE
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem finrank_eq (G : GDatum) : Module.finrank G.F (ℚ ⊗[ℤ] G.O) = G.m ^ 2 := by
  haveI := G.freeO
  haveI := G.finO
  have h1 : Module.finrank ℚ (ℚ ⊗[ℤ] G.O) = Module.finrank ℤ G.O := Module.finrank_baseChange
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] G.O) := inferInstance
  haveI : Module.Finite G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  have h2 := Module.finrank_mul_finrank ℚ G.F (ℚ ⊗[ℤ] G.O)
  rw [h1, G.rankO] at h2
  have hd : 0 < Module.finrank ℚ G.F := Module.finrank_pos
  have : Module.finrank ℚ G.F * Module.finrank G.F (ℚ ⊗[ℤ] G.O) = Module.finrank ℚ G.F * G.m ^ 2 := by
    rw [h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hd this

theorem isCentral (G : GDatum) : Algebra.IsCentral G.F (ℚ ⊗[ℤ] G.O) := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G z
  have hxc : ∀ y : G.O, x * y = y * x := by
    intro y
    apply GDatum.tmul_one_injective G
    have e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (z * (1 ⊗ₜ y)) := by
      rw [← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * z) := by
      rw [← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)
    rw [e1, e2, hz]
  obtain ⟨c, e, he, hec⟩ := G.central x hxc
  have hM : ((e * N : ℤ) : ℚ) • z = algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) := by
    rw [algebraMap_F_coe, ← hec, Int.cast_smul_eq_zsmul, mul_smul, hx, TensorProduct.tmul_smul]
  have hq : ((e * N : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero he hN
  refine ⟨((e * N : ℤ) : ℚ)⁻¹ • (c : G.F), ?_⟩
  show algebraMap G.F (ℚ ⊗[ℤ] G.O) (((e * N : ℤ) : ℚ)⁻¹ • (c : G.F)) = z
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, ← hM, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem ordB_finite (G : GDatum) : Module.Finite ℤ (ordB G) := by
  haveI := G.finO
  let f := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom
  exact Module.Finite.of_surjective f.rangeRestrict.toIntAlgHom.toLinearMap f.rangeRestrict_surjective

theorem ordB_denom (G : GDatum) (b : ℚ ⊗[ℤ] G.O) : ∃ n : ℕ, 0 < n ∧ (n : ℚ ⊗[ℤ] G.O) * b ∈ ordB G := by
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G b
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
  · refine ⟨n, by omega, x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] x = _
    rw [← hx, natCast_zsmul, nsmul_eq_mul]
  · refine ⟨n, by omega, -x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] (-x) = _
    rw [TensorProduct.tmul_neg, ← hx, neg_smul, neg_neg, natCast_zsmul, nsmul_eq_mul]

theorem splitAE : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M →
    Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  intro G
  haveI := G.freeO
  haveI := G.finO
  haveI := isCentral G
  haveI := GDatum.isSimpleRing G
  haveI : FiniteDimensional G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  obtain ⟨N, hN, hloc⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F (ℚ ⊗[ℤ] G.O) G.m (finrank_eq G) (ordB G) (ordB_finite G) (ordB_denom G)
  refine ⟨N, hN, fun p _ hp => ?_⟩
  obtain ⟨ψ, hψ⟩ := hloc p hp
  obtain ⟨ι, hι⟩ : ∃ ι : G.O ⊗[ℤ] ℤ_[p] ≃+* locOrder p (ordB G),
      ∀ o : G.O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) = (1 : ℚ_[p]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) :=
    GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite G.O p
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin G.F p
  let Φ : G.O ⊗[ℤ] ℤ_[p] ≃+* Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p]) :=
    ι.trans (ψ.toRingEquiv.trans κ.symm.mapMatrix)
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) fun c => ?_⟩
  obtain ⟨h, hh⟩ := hψ (κ (c ⊗ₜ[ℤ] 1))
  have e1 : ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) = ⟨_, h⟩ := by
    apply Subtype.ext
    show (ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) =
      cenMap p G.F (ℚ ⊗[ℤ] G.O) (κ (c ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] G.F)
    rw [Algebra.TensorProduct.algebraMap_apply, hι, hκ, cenMap, Algebra.TensorProduct.map_tmul]
    show _ = (1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F)
    rw [algebraMap_F_coe]
  show κ.symm.mapMatrix (ψ (ι _)) = _
  rw [e1]
  erw [hh]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.algebraMap_eq_diagonal]
  split_ifs <;> simp [RingEquiv.symm_apply_apply]

end GlobalTheory.UPel.HT.Gen.SplitAE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open TensorProduct Formalism.UG Formalism.UG.P

namespace GlobalTheory.OpenChrRam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_natCast_mem (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    (N : v.adicCompletion F) ≠ 0 ∧ (N : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (N : v.adicCompletion F) = 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) := by simp
    have e2 : v.valuation F (algebraMap (𝓞 F) F (N : 𝓞 F)) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hN
    rw [← e2, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact congrArg _ e
  refine ⟨fun h => by rw [h] at h1; simp at h1, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem inertAt_le_congN (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  rintro x ⟨⟨hx, hx'⟩, hs⟩
  obtain ⟨hN0, hNi⟩ := inv_natCast_mem v N hN
  let u : (RInt F E)ˣ := ⟨⟨x, hx⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx'⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  have hn : (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, afsplitI_mem_intAd v _ hNi⟩, rfl⟩)
  refine (mem_kerRed _ u).2 (Ideal.mem_span_singleton'.2 ⟨⟨_, hn⟩ * ((u : RInt F E) - 1), ?_⟩)
  apply Subtype.ext
  show (1 : E) ⊗ₜ[F] afsplitI v (N : v.adicCompletion F)⁻¹ * ((x : AfE F E) - 1) * ((N : RInt F E) : AfE F E)
    = (x : AfE F E) - 1
  rw [SubringClass.coe_natCast, ← sub_eq_zero]
  refine afsplit_inj _ fun w => ?_
  rw [map_sub, map_mul, map_mul, afsplit_prV_tmul, map_natCast]
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, mul_right_comm]
    have : (1 : E) ⊗ₜ[F] (N : w.adicCompletion F)⁻¹ * (N : E ⊗[F] w.adicCompletion F) = 1 := by
      have e : (N : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ[F] (N : w.adicCompletion F) :=
        (map_natCast (Algebra.TensorProduct.includeRight :
          w.adicCompletion F →ₐ[F] E ⊗[F] w.adicCompletion F) N).symm
      rw [e, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hN0, one_mul]
      rfl
    rw [this, one_mul, sub_self]
  · have hw : prV (E := E) w (x : AfE F E) = 1 := by
      have h1 := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hs w) h
      exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
    rw [map_sub, hw, map_one, sub_self, mul_zero, zero_mul, sub_self]

theorem qprime_finite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (L : Type) [Field L] (ξ : Chr F E L) (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have hne : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  by_contra hc
  refine hv ((inertAt_le_congN v N fun hm => hc ?_).trans hk)
  exact Ideal.dvd_span_singleton.2 hm

end GlobalTheory.OpenChrRam
end

