module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotGraded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial DirectSum

noncomputable section

universe u

section QuotDecomposition

variable {ι R A : Type*} [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [Decomposition 𝒜] (I : Ideal A)

def quotPieces (n : ι) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

omit [DecidableEq ι] [Decomposition 𝒜] in
theorem mk_mem_quotPieces {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ quotPieces 𝒜 I n :=
  ⟨a, ha, rfl⟩

def quotPieceMap (n : ι) : 𝒜 n →+ quotPieces 𝒜 I n where
  toFun x := ⟨Ideal.Quotient.mk I x, mk_mem_quotPieces 𝒜 I x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def quotientDecomposition : A →+ ⨁ n, quotPieces 𝒜 I n :=
  (DirectSum.map (quotPieceMap 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

variable {𝒜 I}

theorem quotientDecomposition_apply (a : A) : quotientDecomposition 𝒜 I a =
    DirectSum.map (quotPieceMap 𝒜 I) (DirectSum.decompose 𝒜 a) := rfl

theorem quotientDecomposition_of_mem_ideal (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) {a : A}
    (ha : a ∈ I) : quotientDecomposition 𝒜 I a = 0 := by
  ext n
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a n : A) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI n a ha

omit [Decomposition 𝒜] in
theorem coe_comp_map_quotPieceMap :
    (DirectSum.coeAddMonoidHom (quotPieces 𝒜 I)).comp (DirectSum.map (quotPieceMap 𝒜 I)) =
      (Ideal.Quotient.mk I).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
  ext n x
  simp [DirectSum.map_of, quotPieceMap]

theorem coe_quotientDecomposition (a : A) :
    DirectSum.coeAddMonoidHom (quotPieces 𝒜 I) (quotientDecomposition 𝒜 I a) = Ideal.Quotient.mk I a := by
  rw [quotientDecomposition_apply]
  have := congrArg (fun φ => φ (DirectSum.decompose 𝒜 a)) (coe_comp_map_quotPieceMap (𝒜 := 𝒜) (I := I))
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact congrArg (Ideal.Quotient.mk I) ((DirectSum.decompose 𝒜).symm_apply_apply a)

theorem quotientDecomposition_of_mem_piece {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    quotientDecomposition 𝒜 I a = DirectSum.of (fun n => quotPieces 𝒜 I n) n
      ⟨Ideal.Quotient.mk I a, mk_mem_quotPieces 𝒜 I ha⟩ := by
  rw [quotientDecomposition_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl

def quotDecomp (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    A ⧸ I →+ ⨁ n, quotPieces 𝒜 I n :=
  QuotientAddGroup.lift I.toAddSubgroup (quotientDecomposition 𝒜 I)
    (fun _ ha => AddMonoidHom.mem_ker.mpr (quotientDecomposition_of_mem_ideal hI ha))

@[instance_reducible]
def quotDecomposition (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    Decomposition (quotPieces 𝒜 I) where
  decompose' := quotDecomp hI
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => exact coe_quotientDecomposition a
  right_inv d := by
    induction d using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of n q =>
      obtain ⟨q, a, ha, rfl⟩ := q
      rw [DirectSum.coeAddMonoidHom_of]
      exact quotientDecomposition_of_mem_piece ha
    | add d e hd he => rw [map_add (f := _), map_add (f := _), hd, he]

theorem quotPieces_isInternal (hI : ∀ (n : ι) (a : A), a ∈ I → (decompose 𝒜 a n : A) ∈ I) :
    IsInternal (quotPieces 𝒜 I) :=
  letI := quotDecomposition hI
  Decomposition.isInternal _

end QuotDecomposition

section PolyQuot

variable {S : Type u} [CommRing S] {N : ℕ}

theorem weight_one_int (d : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = (d.degree : ℤ) := by
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, nsmul_eq_mul, mul_one]
  change _ = ((∑ i ∈ d.support, d i : ℕ) : ℤ)
  push_cast
  rfl

theorem isHomogeneous_of_isWeightedHomogeneous_one {f : Poly S N} {n : ℕ}
    (hf : IsWeightedHomogeneous (fun _ => (1 : ℤ)) f (n : ℤ)) : f.IsHomogeneous n := by
  intro d hd
  have h1 := hf hd
  rw [weight_one_int] at h1
  have h2 : Finsupp.weight (1 : Fin (N + 1) → ℕ) d = d.degree := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [h2]
  exact_mod_cast h1

theorem weightedHomogeneousComponent_one_mem {p : Ideal (Poly S N)}
    (hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p) (c : ℤ) {f : Poly S N} (hf : f ∈ p) :
    weightedHomogeneousComponent (fun _ => (1 : ℤ)) c f ∈ p := by
  by_cases hc : 0 ≤ c
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    have : weightedHomogeneousComponent (fun _ => (1 : ℤ)) (k : ℤ) f = homogeneousComponent k f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, weight_one_int]
      simp only [Nat.cast_inj]
    rw [this]
    exact hp f hf k
  · have : weightedHomogeneousComponent (fun _ => (1 : ℤ)) c f = 0 := by
      ext d
      rw [coeff_weightedHomogeneousComponent, weight_one_int, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      split_ifs with h
      · omega
      · rfl
    rw [this]
    exact p.zero_mem

def quotGraded (p : Ideal (Poly S N)) (hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p) :
    GradedPMod S N (Poly S N ⧸ p) where
  piece := quotPieces (weightedHomogeneousSubmodule S (fun _ : Fin (N + 1) => (1 : ℤ))) p
  isInternal := by
    classical
    let _ := weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))
    refine quotPieces_isInternal fun n a ha => ?_
    have h := weightedDecomposition.decompose'_apply S (fun _ : Fin (N + 1) => (1 : ℤ)) a n
    change ((weightedDecomposition S (fun _ : Fin (N + 1) => (1 : ℤ))).decompose' a n :
      Poly S N) ∈ p
    rw [h]
    exact weightedHomogeneousComponent_one_mem hp n ha
  smul_mem d c q m hq hm := by
    obtain ⟨f, hf, rfl⟩ := hm
    refine ⟨q * f, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule, add_comm c (d : ℤ)]
      exact (isWeightedHomogeneous_int_of_isHomogeneous hq).mul hf
    · change Ideal.Quotient.mk p (q * f) = q • Ideal.Quotient.mk p f
      rfl

theorem mem_quotGraded_piece {p : Ideal (Poly S N)} {hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p}
    {c : ℤ} {m : Poly S N ⧸ p} :
    m ∈ (quotGraded p hp).piece c ↔ ∃ f : Poly S N,
      IsWeightedHomogeneous (fun _ => (1 : ℤ)) f c ∧ Ideal.Quotient.mk p f = m := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩

theorem finite_quot (p : Ideal (Poly S N)) : Module.Finite (Poly S N) (Poly S N ⧸ p) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ (Poly S N) p).toLinearMap
    Ideal.Quotient.mk_surjective

end PolyQuot

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial TensorProduct

noncomputable section

universe u v w

def CechExact.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M' M M'' : Type v)
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M''] [Module (Poly S N) M''] [Module S M''] [IsScalarTower S (Poly S N) M'']
    (𝓜' : GradedPMod S N M') (𝓜 : GradedPMod S N M) (𝓜'' : GradedPMod S N M'')
    (f : GradedHom 𝓜' 𝓜) (g : GradedHom 𝓜 𝓜''),
    Function.Injective f.toLin → Function.Surjective g.toLin → Function.Exact f.toLin g.toLin →
    ∀ c : ℤ, Function.Injective (cohomMap f 0 c) ∧
      ∀ i : ℕ, Function.Exact (cohomMap f i c) (cohomMap g i c) ∧
        ∃ δ : cohom 𝓜'' i c →ₗ[S] cohom 𝓜' (i + 1) c,
          Function.Exact (cohomMap g i c) δ ∧ Function.Exact δ (cohomMap f (i + 1) c)

def CechTop.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M) (i : ℕ) (c : ℤ), N < i → Subsingleton (cohom 𝓜 i c)

def Extension.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (F : SubFamily S x E), (∀ I, (F.sub I).FG) →
    ∃ M : FinGradedSub (S := S) (x := x) E, (∀ c, M.piece c ≤ F.gam c) ∧ ∀ I, M.tilde 0 I = F.sub I

def Generated.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x),
    ∃ c₀ : ℤ, ∀ c ≥ c₀, (Q.twist (twistSys S x c)).Generated

def GeneratedAmple.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x), AmpleData S x H → ∀ Q : LineBundle S x,
    ∃ c₀ : ℕ, ∀ c ≥ c₀, (Q.twist (H.pow c)).Generated

def PrimeFiltration.Exists.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M → (∀ p ∈ primeOf (S := S) x, ∀ m : M, p • m = 0) →
    Nonempty (PrimeFilt 𝓜) ∧
      ∀ (F : PrimeFilt 𝓜) (pp : Ideal (Poly S N)) [pp.IsPrime],
        pp ∈ (Module.annihilator (Poly S N) M).minimalPrimes →
        (((Finset.univ.filter fun k => F.prime k = pp).card : ℕ) : ℕ∞) =
          Module.length (Localization.AtPrime pp) (LocalizedModule pp.primeCompl M)

def PrimeFiltration.Point.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → primeOf (S := S) x ≤ pp →
    ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly S N) ∉ pp →
    (chartPrime pp hj).IsPrime ∧
      ∀ (K' : Type w) [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K'),
        RingHom.ker ψ = chartPrime pp hj → primeOf (S := S) (fun i => ψ (ratio hj i)) = pp

def PrimeFiltration.Restrict.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → primeOf (S := S) x ≤ pp →
    ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly S N) ∉ pp →
    ∀ (K' : Type w) [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K'),
      RingHom.ker ψ = chartPrime pp hj →
      ∀ (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0) (Q : LineBundle S x),
        ∃ (Q' : LineBundle S (fun i => ψ (ratio hj i))) (r : Ω → K'),
          ∀ I : Chart (fun i => ψ (ratio hj i)),
            (∀ q ∈ Q.sub (liftChart hxy I), r q ∈ Q'.sub I) ∧
            (∀ q ∈ Q.sub (liftChart hxy I), ∀ q' ∈ Q.sub (liftChart hxy I), r (q + q') = r q + r q') ∧
            (∀ q ∈ Q.sub (liftChart hxy I), ∀ (f s : Poly S N) (e : ℕ), s ∈ monos I.1 →
              f.IsHomogeneous e → s.IsHomogeneous e →
              r (aeval x f / aeval x s * q) =
                aeval (fun i => ψ (ratio hj i)) f / aeval (fun i => ψ (ratio hj i)) s * r q) ∧
            Submodule.span (chartRing S (fun i => ψ (ratio hj i)) I) (r '' Q.sub (liftChart hxy I)) =
              Q'.sub I

def SerrePoly.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ),
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (cohom (polyGraded S N) i c)) ∧
    ∀ c : ℤ, 0 ≤ c → (∀ i, 1 ≤ i → Subsingleton (cohom (polyGraded S N) i c)) ∧
      Function.Bijective (toH0 (polyGraded S N) c)

def SerreFree.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M) (r : ℕ) (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ),
    (∀ j, b j ∈ 𝓜.piece (d j)) →
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (cohom 𝓜 i c)) ∧
    ∀ c : ℤ, (∀ j, d j ≤ c) → (∀ i, 1 ≤ i → Subsingleton (cohom 𝓜 i c)) ∧
      Function.Bijective (toH0 𝓜 c)

def SerreFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∀ (i : ℕ) (c : ℤ), Module.Finite S (cohom 𝓜 i c)

def SerreVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ i, 1 ≤ i → ∀ c ≥ c₀, Subsingleton (cohom 𝓜 i c)

def SerreOnto.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ c ≥ c₀, Function.Surjective (toH0 𝓜 c)

def SerreTail.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M → ∀ c₁ : ℤ,
    ∃ t : Finset (Cech.Cochain (locSys S N M) 0), (∀ z ∈ t, z ∈ H0tail 𝓜 c₁) ∧
      H0tail 𝓜 c₁ ≤ (Submodule.span (Poly S N) (t : Set (Cech.Cochain (locSys S N M) 0))).restrictScalars S

def TwistFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (G B : LineBundle S x) (r : ℕ) (η : Fin (r + 1) → Ω), x ≠ 0 →
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ (n : ℕ) (deg : Fin n → ℕ) (gen : Fin n → Ω),
      (∀ k, gen k ∈ (G.twist (B.pow (deg k))).secs) ∧
      ∀ b : ℕ, (G.twist (B.pow b)).secs ≤ Submodule.span S {z | ∃ (k : Fin n)
        (f : MvPolynomial (Fin (r + 1)) S) (e : ℕ), f.IsHomogeneous e ∧ e + deg k = b ∧
        z = aeval η f * gen k}

def TwistVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (G B : LineBundle S x) (r : ℕ) (η : Fin (r + 1) → Ω),
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c →
      Subsingleton (((G.twist (B.pow b)).twist (twistSys S x c)).H 1)

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

theorem twist_hyps {Ω : Type w} [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω) :
    (∀ j, x j ∈ (twistBundle k x 1).secs) ∧
    ∀ I, Submodule.span (chartRing k x I) (Set.range x) = (twistBundle k x 1).sub I :=
  ⟨mem_secs_twistBundle_one, span_range_eq_twistMod_one⟩

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def AmpleCover.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (F : SubSystem S x Ω),
    (∀ (j : Fin (A.r + 1)) (I : Chart x) (y : Ω), y ∈ F.sub I → ∃ e : ℕ,
      y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) (F.secs : Set Ω) * (H.pow (A.m * e)).sub I) →
    F.Generated

def AmpleTwistLocal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)),
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (I : Chart x) (y : Ω), y ∈ (Q.twist (H.pow (b + A.m * n))).sub I →
      ∃ e : ℕ, y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) ((Q.twist (H.pow (b + A.m * n))).secs : Set Ω) *
          (H.pow (A.m * e)).sub I

section Hypotheses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω)

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmpleAffine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def AmpleAffineGen.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)), A.h j ≠ 0 →
    ∃ (p : ℕ) (s : Fin p → Ω),
      (∀ (t : Fin p) (I : Chart x), ∃ k : ℕ,
        s t * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I) ∧
      ∀ (I : Chart x) (z : Ω) (k : ℕ), z * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I →
        ∃ (e : ℕ) (g : Fin p → Ω), (∀ t, g t * A.h j ^ e ∈ (H.pow (A.m * e)).sub I) ∧
          z = ∑ t, g t * s t

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCechDSq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

def CechDSq.Statement : Prop :=
  ∀ (n : ℕ) (U : Finset (Fin n)) (R : Type u) [CommRing R] (G : Cell U → Type v)
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J),
    (∀ (I J K : Cell U) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1),
      (ρ J K hJK).comp (ρ I J hIJ) = ρ I K (hIJ.trans hJK)) →
    ∀ (i : ℕ) (s : Cech.Cochain G i), Cech.d G ρ (i + 1) (Cech.d G ρ i s) = 0

section Hypotheses

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

theorem locResS_comp (I J K : StdCell N) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (locResS (S := S) (M := M) J K hJK).comp (locResS I J hIJ) = locResS I K (hIJ.trans hJK) := by
  refine LinearMap.ext fun x => ?_
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locRes hJK (locRes hIJ _) = locRes (hIJ.trans hJK) _
    rw [locRes_mk, locRes_mk, locRes_mk]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def TwistSections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (y : Fin (N + 1) → Ω), y ≠ 0 →
    ∀ᶠ n : ℕ in Filter.atTop, (twistSys S y (n : ℤ)).secs = (coordGraded S y).piece (n : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

