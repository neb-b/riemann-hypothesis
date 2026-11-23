module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.StarRingOfInvolution

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.IsUnimodIffGram
section
namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem isHerm_iff_gram {ι : Type*} [Fintype ι] (h : Sesq R M) (b : Module.Basis ι R M) :
    IsHerm h ↔ (gram h b).IsHermitian := by
  constructor
  · intro hh
    ext i j
    simp only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact (hh (b j) (b i)).symm
  · intro hG x y
    have hb : ∀ i j, star (h (b i) (b j)) = h (b j) (b i) := fun i j => by
      have := congrFun (congrFun hG j) i
      simpa [gram, Matrix.conjTranspose_apply] using this
    rw [← b.sum_repr x, ← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply,
      starRingEnd_apply, smul_eq_mul, star_sum, star_mul', star_star, hb, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem isUnimod_iff_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Sesq R M)
    (b : Module.Basis ι R M) : IsUnimod h ↔ IsUnit (gram h b).det := by
  have hmv : Function.Bijective (gram h b).mulVec ↔ IsUnit (gram h b).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    refine ⟨fun hb => hb.2, fun hs => ⟨?_, hs⟩⟩
    have hu : IsUnit (gram h b).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hs)
    intro v w hvw
    have := congrArg (gram h b)⁻¹.mulVec hvw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
  have hcomp : (b.dualBasis.equivFun ∘ (LinearMap.flip h) ∘ b.equivFun.symm) =
      (gram h b).mulVec ∘ star := by
    funext v i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Module.Basis.equivFun_symm_apply, Module.Basis.dualBasis_repr, gram, Matrix.mulVec, dotProduct,
      map_sum, map_smulₛₗ, mul_comm, starRingEnd_apply]
  have hfl : Function.Bijective (LinearMap.flip h) ↔ Function.Bijective ((gram h b).mulVec ∘ star) := by
    rw [← hcomp, EquivLike.comp_bijective, EquivLike.bijective_comp]
  rw [IsUnimod, hfl, Function.Bijective.of_comp_iff _ (Function.Involutive.bijective star_involutive), hmv]

theorem gram_comb {ι κ : Type*} [Fintype κ] (h : Sesq R M) (x : κ → M) (P : Matrix ι κ R) :
    gram h (fun i => ∑ j, P i j • x j) = P * gram h x * P.conjTranspose := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    starRingEnd_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end KStar.Cstarloc
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.UnitVector
section
namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

private theorem norm_one_of_unit (hR : UnramDatum R) (h : Sesq R M) (hh : IsHerm h) (z : M)
    (hz : IsUnit (h z z)) : ∃ x, h x x = 1 := by
  obtain ⟨a, ha⟩ := hR.norm_onto (h z z) hz (hh z z).symm
  have hau : IsUnit a := isUnit_of_mul_isUnit_left (ha ▸ hz)
  obtain ⟨u, rfl⟩ := hau
  refine ⟨(↑u⁻¹ : R) • z, ?_⟩
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← ha]
  have h1 : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
  have h2 : star (↑u⁻¹ : R) * star (↑u : R) = 1 := by rw [← star_mul', Units.inv_mul, star_one]
  linear_combination (star (↑u⁻¹ : R) * star (↑u : R)) * h1 + h2

theorem exists_norm_one [IsLocalRing R] (hR : UnramDatum R) [Module.Free R M] [Nontrivial M]
    (h : Sesq R M) (hh : IsHerm h) (hu : IsUnimod h) : ∃ x, h x x = 1 := by
  obtain ⟨e, he⟩ := hR.trace_one
  let b := Module.Free.chooseBasis R M
  have : Nonempty (Module.Free.ChooseBasisIndex R M) := b.index_nonempty
  obtain ⟨i⟩ := this
  obtain ⟨y, hy⟩ := hu.2 (b.coord i)
  have hxy : h (b i) y = 1 := by
    have := LinearMap.congr_fun hy (b i)
    simpa using this
  have hyx : h y (b i) = 1 := by rw [hh (b i) y, hxy, star_one]
  by_cases hx : IsUnit (h (b i) (b i))
  · exact norm_one_of_unit hR h hh _ hx
  by_cases hyy : IsUnit (h y y)
  · exact norm_one_of_unit hR h hh _ hyy
  refine norm_one_of_unit hR h hh (b i + e • y) ?_
  have key : h (b i + e • y) (b i + e • y) = 1 + (h (b i) (b i) + e * star e * h y y) := by
    simp only [map_add (f := _), map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hxy, hyx]
    linear_combination he
  have hw : ¬ IsUnit (e * star e * h y y) := fun hw => hyy (isUnit_of_mul_isUnit_right hw)
  have hs : ¬ IsUnit (h (b i) (b i) + e * star e * h y y) :=
    IsLocalRing.nonunits_add (mem_nonunits_iff.mpr hx) (mem_nonunits_iff.mpr hw)
  rw [key]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (show (1 + (h (b i) (b i) + e * star e * h y y)) + -(h (b i) (b i) + e * star e * h y y) = 1 by ring)
    with h' | h'
  · exact h'
  · exact absurd (by simpa using h'.neg) hs

private theorem sub_mem_perp (h : Sesq R M) (x : M) (hx : h x x = 1) (z : M) :
    z - h z x • x ∈ perp h x := by
  rw [mem_perp]
  simp [map_sub, map_smul, hx]

theorem isUnimod_restr_perp (h : Sesq R M) (hh : IsHerm h) (hu : IsUnimod h) (x : M)
    (hx : h x x = 1) : IsUnimod (restr h (perp h x)) := by
  have hperp : ∀ n ∈ perp h x, h x n = 0 := fun n hn => by
    rw [mem_perp] at hn
    rw [hh n x, hn, star_zero]
  constructor
  · intro n1 n2 heq
    have hsub : ∀ m : perp h x, h m ((n1 : M) - n2) = 0 := fun m => by
      have := LinearMap.congr_fun heq m
      simp only [LinearMap.flip_apply, restr, LinearMap.domRestrict₁₂_apply] at this
      rw [map_sub, this, sub_self]
    have hxn : h x ((n1 : M) - n2) = 0 := hperp _ (Submodule.sub_mem _ n1.2 n2.2)
    have hall : LinearMap.flip h ((n1 : M) - n2) = LinearMap.flip h 0 := by
      ext z
      simp only [LinearMap.flip_apply, map_zero, LinearMap.zero_apply]
      have hz := hsub ⟨z - h z x • x, sub_mem_perp h x hx z⟩
      have hdec : h z = h (z - h z x • x) + h z x • h x := by
        rw [map_sub, map_smul, sub_add_cancel]
      rw [hdec, LinearMap.add_apply, LinearMap.smul_apply, hxn, smul_zero, add_zero]
      simpa using hz
    exact Subtype.ext (sub_eq_zero.mp (hu.1 hall))
  · intro f
    let P : M →ₗ[R] perp h x := (LinearMap.id - (LinearMap.flip h x).smulRight x).codRestrict (perp h x)
      (fun z => by simpa using sub_mem_perp h x hx z)
    obtain ⟨y, hy⟩ := hu.2 (f ∘ₗ P)
    have hPm : ∀ m : perp h x, P m = m := fun m => Subtype.ext (by simp [P, (mem_perp h x m).mp m.2])
    have hPx : P x = 0 := Subtype.ext (by simp [P, hx])
    have h1 : h x y = 0 := by
      have := LinearMap.congr_fun hy x
      simpa [hPx] using this
    have hyx : h y x = 0 := by rw [hh x y, h1, star_zero]
    refine ⟨⟨y, (mem_perp h x y).mpr hyx⟩, ?_⟩
    ext m
    have := LinearMap.congr_fun hy m
    simp [restr, hPm] at this ⊢
    exact this

end KStar.Cstarloc
end

