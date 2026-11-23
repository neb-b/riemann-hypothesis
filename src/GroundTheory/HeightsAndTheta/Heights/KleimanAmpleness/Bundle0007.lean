module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsPres
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTransport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech

theorem Transport.proof : Transport.Statement.{u, v, w} := by
  intro n U R _ G _ _ G' _ _ ρ ρ' deg deg' φ hφ hdeg hinj hmap i

  have minj : ∀ i, Function.Injective (mapC (G := G) (G' := G') φ i) :=
    fun i s t h => funext fun I => hinj I.1 (congrFun h I)

  have lift : ∀ (i : ℕ) (w' : Cochain G' i), w' ∈ Cdeg G' deg' i →
      ∃ w ∈ Cdeg G deg i, mapC φ i w = w' := by
    intro i w' hw'
    have h : ∀ I : Idx U i, ∃ x ∈ deg I.1, φ I.1 x = w' I := fun I => by
      have hI : w' I ∈ deg' I.1 := hw' I (Set.mem_univ _)
      rw [← hmap I.1] at hI
      exact Submodule.mem_map.mp hI
    choose w hw hφw using h
    exact ⟨w, fun I _ => hw I, funext fun I => hφw I⟩

  have bdry : ∀ (i : ℕ) (z : Cochain G i), mapC φ i z ∈ bdryDeg G' deg' ρ' i → z ∈ bdryDeg G deg ρ i := by
    intro i z h
    cases i with
    | zero =>
      change mapC φ 0 z ∈ (⊥ : Submodule R _) at h
      change z ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot] at h ⊢
      exact minj 0 (h.trans (map_zero _).symm)
    | succ i =>
      change mapC φ (i + 1) z ∈ (Cdeg G' deg' i).map (d G' ρ' i) at h
      change z ∈ (Cdeg G deg i).map (d G ρ i)
      obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
      obtain ⟨w, hw, rfl⟩ := lift i w' hw'
      refine Submodule.mem_map.mpr ⟨w, hw, minj (i + 1) ?_⟩
      rw [mapC_d φ hφ]
      exact hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk _ = 0 at hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (bdry i z hx')
  · intro y
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨w, hw, hwz⟩ := lift i z' z'.2.2
    have hdw : d G ρ i w = 0 := by
      apply minj (i + 1)
      rw [mapC_d φ hφ, hwz, map_zero]
      exact z'.2.1
    refine ⟨Submodule.Quotient.mk ⟨w, hdw, hw⟩, ?_⟩
    change Submodule.Quotient.mk _ = _
    congr 1
    exact Subtype.ext hwz

end Cech

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDegLocExact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

namespace DegLocExact

theorem decompose_map {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i) (a : A) (k : ι) :
    φ (DirectSum.decompose 𝒜 a k) = DirectSum.decompose ℬ (φ a) k := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [h0]
  | @homogeneous i m =>
    obtain ⟨m, hm⟩ := m
    by_cases hik : i = k
    · subst hik
      rw [DirectSum.decompose_of_mem_same (ℳ := 𝒜) hm,
        DirectSum.decompose_of_mem_same (ℳ := ℬ) (hφ _ _ hm)]
    · rw [DirectSum.decompose_of_mem_ne (ℳ := 𝒜) hm hik,
        DirectSum.decompose_of_mem_ne (ℳ := ℬ) (hφ _ _ hm) hik, h0]
  | add m m' hm hm' => simp [hadd, DirectSum.decompose_add, hm, hm']

theorem mem_of_map_mem {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i)
    (hinj : Function.Injective φ) {a : A} {k : ι} (ha : φ a ∈ ℬ k) : a ∈ 𝒜 k := by
  have h := decompose_map 𝒜 ℬ φ h0 hadd hφ a k
  rw [DirectSum.decompose_of_mem_same (ℳ := ℬ) ha] at h
  rw [← hinj h]
  exact SetLike.coe_mem _

variable {S : Type u} [CommRing S] {N : ℕ} {M : Type v} [AddCommGroup M] [Module (Poly S N) M]
  [Module S M] [IsScalarTower S (Poly S N) M]

theorem exists_frac (𝓜 : GradedPMod S N M) (c : ℤ) (I : StdCell N) (z : LocMod S N M I.1)
    (hz : z ∈ degLoc 𝓜 c I) :
    ∃ (m : M) (s : monos (S := S) I.1) (e : ℕ), (s : Poly S N).IsHomogeneous e ∧
      m ∈ 𝓜.piece (c + e) ∧ z = (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, s, a, e, hm, hs, hae, rfl⟩ := hz
    exact ⟨m, s, e, hs, by rwa [← hae, sub_add_cancel], rfl⟩
  | zero => exact ⟨0, 1, 0, isHomogeneous_one _ _, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, s1, e1, hs1, hm1, rfl⟩ := hx
    obtain ⟨m2, s2, e2, hs2, hm2, rfl⟩ := hy
    refine ⟨(s2 : Poly S N) • m1 + (s1 : Poly S N) • m2, s1 * s2, e1 + e2,
      by simpa using hs1.mul hs2, add_mem ?_ ?_, LocalizedModule.mk_add_mk⟩
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e1 + e2 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e2 _ _ m1 hs2 hm1
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e2 + e1 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e1 _ _ m2 hs1 hm2
  | smul r x _ hx =>
    obtain ⟨m, s, e, hs, hm, rfl⟩ := hx
    refine ⟨r • m, s, e, hs, Submodule.smul_mem _ r hm, ?_⟩
    change algebraMap S (Poly S N) r • (LocalizedModule.mk m s : LocalizedModule _ M) = _
    rw [LocalizedModule.smul'_mk, algebraMap_smul]

theorem proof : DegLocExact.Statement := by
  intro S _ N M' M M'' _ _ _ _ _ _ _ _ _ _ _ _ 𝓜' 𝓜 𝓜'' f g hf hg hfg c I
  let _ := 𝓜'.isInternal.chooseDecomposition
  let _ := 𝓜.isInternal.chooseDecomposition
  let _ := 𝓜''.isInternal.chooseDecomposition
  refine ⟨fun z hz hz0 => ?_, fun z hz => ?_⟩
  · obtain ⟨m, s, e, hs, hm, rfl⟩ := exists_frac 𝓜 c I z hz
    rw [locMap_mk] at hz0
    have h0 : (LocalizedModule.mk (g.toLin m) s : LocalizedModule (monos (S := S) I.1) M'') =
        LocalizedModule.mk 0 s := by rw [LocalizedModule.zero_mk]; exact hz0
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 h0
    set T : monos (S := S) I.1 := u * s with hT
    obtain ⟨e', he'⟩ := monos_isHomogeneous T.2
    have hgT : g.toLin ((T : Poly S N) • m) = 0 := by
      rw [map_smul, hT, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← Submonoid.smul_def,
        hu, smul_zero, smul_zero]
    obtain ⟨m', hm'⟩ := (hfg _).1 hgT
    have hTm : (T : Poly S N) • m ∈ 𝓜.piece (c + e + e') := 𝓜.smul_mem e' _ _ m he' hm
    have hm'd : m' ∈ 𝓜'.piece (c + e + e') :=
      mem_of_map_mem 𝓜'.piece 𝓜.piece f.toLin (map_zero _) (map_add _) f.map_piece hf (hm' ▸ hTm)
    refine ⟨LocalizedModule.mk m' (T * s), Submodule.subset_span
      ⟨m', T * s, c + e + e', e' + e, hm'd, by simpa using he'.mul hs, by push_cast; ring, rfl⟩, ?_⟩
    rw [locMap_mk, hm', ← Submonoid.smul_def, LocalizedModule.mk_cancel_common_left]
  · obtain ⟨m'', s, e, hs, hm'', rfl⟩ := exists_frac 𝓜'' c I z hz
    obtain ⟨m, rfl⟩ := hg m''
    refine ⟨LocalizedModule.mk (DirectSum.decompose 𝓜.piece m (c + e) : M) s, Submodule.subset_span
      ⟨_, s, c + e, e, SetLike.coe_mem _, hs, by ring, rfl⟩, ?_⟩
    rw [locMap_mk, decompose_map 𝓜.piece 𝓜''.piece g.toLin (map_zero _) (map_add _) g.map_piece,
      DirectSum.decompose_of_mem_same (ℳ := 𝓜''.piece) hm'']

end DegLocExact

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedULift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem GradedULift.proof : GradedULift.Statement.{u, v} := by
  intro S _ N M _ _ _ _ 𝓜
  let e : M ≃ₗ[S] ULift.{u} M := (ULift.moduleEquiv (R := S)).symm
  let eP : M ≃ₗ[Poly S N] ULift.{u} M := (ULift.moduleEquiv (R := Poly S N)).symm
  let pc : ℤ → Submodule S (ULift.{u} M) := fun c => (𝓜.piece c).map (e : M →ₗ[S] ULift.{u} M)
  have hpc : ∀ c, pc c = Submodule.orderIsoMapComap e (𝓜.piece c) := fun _ => rfl
  have hint : DirectSum.IsInternal pc := by
    have h0 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 𝓜.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
    · have : pc = (Submodule.orderIsoMapComap e) ∘ 𝓜.piece := funext hpc
      rw [this]
      exact h0.1.map_orderIso _
    · have h1 : (⨆ c, pc c) = Submodule.orderIsoMapComap e (⨆ c, 𝓜.piece c) := by
        rw [OrderIso.map_iSup]
        rfl
      rw [h1, h0.2]
      exact (Submodule.orderIsoMapComap e).map_top
  let 𝓜' : GradedPMod S N (ULift.{u} M) :=
    { piece := pc
      isInternal := hint
      smul_mem := by
        intro d c p m hp hm
        obtain ⟨x, hx, rfl⟩ := hm
        refine ⟨p • x, 𝓜.smul_mem d c p x hp hx, ?_⟩
        rfl }
  refine ⟨ULift.{u} M, inferInstance, inferInstance, inferInstance, inferInstance, 𝓜',
    ⟨eP.toLinearMap, fun c m hm => ⟨m, hm, rfl⟩⟩,
    ⟨eP.symm.toLinearMap, fun c m hm => ?_⟩, fun m => rfl, fun m => rfl⟩
  obtain ⟨x, hx, rfl⟩ := hm
  exact hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreFinite.proof (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreFinite.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∀ i, N + 1 ≤ i + k → ∀ c : ℤ, Module.Finite S (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _ i hi c
      have := hTop S N M 𝓜 i c (by omega)
      exact ⟨by rw [Subsingleton.elim (⊤ : Submodule S (cohom 𝓜 i c)) ⊥]; exact Submodule.fg_bot⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM i hi c
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      have hF : Module.Finite S (cohom 𝓕 i c) := (hFree S N F 𝓕 r b d hb).1 i c
      have hKf : Module.Finite S (cohom 𝓚 (i + 1) c) := ih K 𝓚 hK (i + 1) (by omega) c
      obtain ⟨-, δ, hδ, -⟩ := (hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i
      refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩
      rw [top_inf_eq, LinearMap.exact_iff.mp hδ, LinearMap.range_eq_map]
      exact hF.fg_top.map _
  intro M _ _ _ _ 𝓜 hM i c
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  have := key (N + 1) M' 𝓜' hM' i (by omega) c
  exact Module.Finite.of_injective (cohomMap f i c) (hRet S N M M' 𝓜 𝓜' f g hgf i c)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u

theorem SerrePoly.proof (hL : SerrePoly.Laurent.Statement.{u}) (hT : Cech.Transport.Statement.{u, u, u})
    (hC : SerrePoly.LaurentCohom.Statement.{u}) : SerrePoly.Statement.{u} := by
  intro S _ _ N
  obtain ⟨hinj, hpiece, ι, hι, hres, hmk, hdeg⟩ := hL S N
  obtain ⟨hfin, hvan, hconst⟩ := hC S N
  have hφ : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N (Poly S N) I.1),
      ι J (locResS I J h m) = Cech.idRes S (Laurent S N) Finset.univ I J h (ι I m) :=
    fun I J h m => hres I J h m
  have hd : ∀ (c : ℤ) (I : StdCell N) (m : LocMod S N (Poly S N) I.1),
      m ∈ degLoc (polyGraded S N) c I → ι I m ∈ laurentDeg S N c I := fun c I m hm => by
    rw [← hdeg c I]; exact Submodule.mem_map_of_mem hm
  have hb : ∀ (i : ℕ) (c : ℤ), Function.Bijective
      (Cech.mapHdeg (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ (hd c) i) :=
    fun i c => hT (N + 1) Finset.univ S _ _ _ _ (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ
      (hd c) hι (hdeg c) i
  let E : ∀ (i : ℕ) (c : ℤ), cohom (polyGraded S N) i c ≃ₗ[S] laurentCohom S N i c :=
    fun i c => LinearEquiv.ofBijective _ (hb i c)
  refine ⟨fun i c => Module.Finite.equiv (E i c).symm, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have := hvan c hc i hi
    exact (E i c).toEquiv.subsingleton
  ·
    intro m m' hmm
    have h0 : (constCochain (S := S) (N := N) (M := Poly S N) (m : Poly S N)) =
        constCochain (S := S) (N := N) (M := Poly S N) (m' : Poly S N) := by
      have hmem := (Submodule.Quotient.eq _).mp hmm
      change _ ∈ (⊥ : Submodule S _).comap _ at hmem
      rw [Submodule.mem_comap, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    let I0 : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{0}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    have h1 := congrArg (ι I0.1) (congrFun h0 I0)
    change ι I0.1 (locMk (Poly S N) I0.1.1 m) = ι I0.1 (locMk (Poly S N) I0.1.1 m') at h1
    rw [hmk, hmk] at h1
    exact Subtype.ext (hinj h1)
  ·
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hw : (Cech.mapC ι 0 (z : Cech.Cochain (locSys S N (Poly S N)) 0)) ∈
        Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
          (Cech.idRes S (Laurent S N) Finset.univ) 0 := by
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, fun I _ => ?_⟩
      · rw [← Cech.mapC_d ι hφ, LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1, map_zero]
      · exact hd c I.1 _ ((Submodule.mem_inf.mp z.2).2 I (Set.mem_univ _))
    obtain ⟨f, hf, hzf⟩ := hconst c hc _ hw
    rw [← hpiece c] at hf
    obtain ⟨m, hm, rfl⟩ := hf
    refine ⟨⟨m, hm⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext I
    apply hι I.1
    change ι I.1 (locMk (Poly S N) I.1.1 m) = _
    rw [hmk]
    exact (hzf I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreVanish.proof (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreVanish.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∃ c₀ : ℤ, ∀ i, N + 1 ≤ i + k → 1 ≤ i → ∀ c ≥ c₀, Subsingleton (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _
      exact ⟨0, fun i hi _ c _ => hTop S N M 𝓜 i c (by omega)⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      obtain ⟨c₁, hc₁⟩ := ih K 𝓚 hK
      refine ⟨max c₁ (∑ j, |d j|), fun i hi hi1 c hc => ?_⟩
      have hdc : ∀ j, d j ≤ c := fun j =>
        ((le_abs_self (d j)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (d j))
          (Finset.mem_univ j))).trans ((le_max_right _ _).trans hc)
      have hF := ((hFree S N F 𝓕 r b d hb).2 c hdc).1 i hi1
      have hKv := hc₁ (i + 1) (by omega) (by omega) c ((le_max_left _ _).trans hc)
      obtain ⟨δ, hδ, -⟩ := ((hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i).2
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : cohom 𝓜 i c, z = 0 := fun z => by
        obtain ⟨w, hw⟩ := (hδ z).mp (Subsingleton.elim _ _)
        rw [← hw, Subsingleton.elim w 0, map_zero]
      rw [hx x, hx y]
  intro M _ _ _ _ 𝓜 hM
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  obtain ⟨c₀, hc₀⟩ := key N M' 𝓜' hM'
  refine ⟨c₀, fun i hi c hc => ?_⟩
  have := hc₀ i (by omega) hi c hc
  exact (hRet S N M M' 𝓜 𝓜' f g hgf i c).subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PointDegreePosSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def PointDegreePos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), IsSubvar (x := x) pp 0 →
    0 < FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Curve.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ G : Ideal (Poly S N), IsSubvar x G 1 → 𝔪.map (C : S →+* Poly S N) ≤ G →
    ∀ᶠ c : ℕ in atTop, interSum G ![M.toSubSystem] c = interNum G ![M.toSubSystem]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

