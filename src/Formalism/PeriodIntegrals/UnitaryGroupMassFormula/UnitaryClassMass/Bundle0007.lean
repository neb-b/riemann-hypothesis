module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSLocA
section
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem resChar {E : Type} [Field E] [NumberField E] (P : Ideal (𝓞 E)) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 E) ∉ P := by
  letI := Ideal.Quotient.field P
  set p := ringChar (𝓞 E ⧸ P)
  haveI : CharP (𝓞 E ⧸ P) p := ringChar.charP _
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hmem : ((Ideal.absNorm P : ℕ) : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  have hN0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hdvd : p ∣ Ideal.absNorm P := (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p _).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hp0 : p ≠ 0 := fun h => hN0 (by rw [h] at hdvd; exact zero_dvd_iff.1 hdvd)
  have hpr : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right hp0
  refine ⟨p, hpr, fun m hm hmP => hm ?_⟩
  exact (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) p m).1 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hmP)

theorem lsLoc : LSLoc := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig g P hP
  classical
  let J := gramOf h b
  set L := crdOf b L0 with hLd

  have hσσ : ∀ e, σ (σ e) = e := fun e => by rw [hσ, hσ, star_star]
  have hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J := by
    show PI.UnitaryApproxDefs.cT (σ : E →+* E) (gramOf h b) = gramOf h b
    ext i j
    simp only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, gramOf]
    have := hs.eq (b j) (b i)
    rw [starRingEnd_apply] at this
    rw [show (σ : E →+* E) (h (b j) (b i)) = σ (h (b j) (b i)) from rfl, hσ]
    exact this
  have hJdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (posDefOfDefiniteSignature_holds M _ (hsig τ)).isUnit
    have e : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [e, h0, map_zero] at hu'
    exact not_isUnit_zero hu'
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹

  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  obtain ⟨m', hm', hmO'⟩ := den_mat (F := F) (E := E) (finMat σ J g⁻¹)

  obtain ⟨p, hpr, hpm⟩ := resChar P hP
  set T : Set (HeightOneSpectrum (𝓞 F)) := {w | (p : 𝓞 F) ∈ w.asIdeal} with hTd
  have hpF : (p : 𝓞 F) ≠ 0 := by exact_mod_cast hpr.ne_zero
  have hfin : T.Finite := (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 F)})
    (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hpF)).subset
      (fun w hw => Ideal.dvd_span_singleton.2 hw)
  have hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal := fun w hw => hw

  set N1 := u * k with hN1
  set N0 := dI * dJ * N1 with hN0
  obtain ⟨γ, hγ⟩ := approxT σ J hσσ hθ hH (isUnit_iff_ne_zero.2 hJdet) g hfin.toFinset (m' * N0)
    (by positivity)
  rw [Set.Finite.coe_toFinset] at hγ
  set ε : Af F ⊗[F] E := evT T ⊗ₜ[F] (1 : E) with hε

  have small1 : ∀ i j, ∃ o ∈ Oh F E,
      ε * (finMat σ J (g⁻¹ * emb σ J γ) - 1) i j = (dI * dJ * N1) • o := by
    choose o ho hoe using hγ
    intro i j
    refine ⟨∑ l, -((m' • finMat σ J g⁻¹ i l) * o l j),
      AddSubgroup.sum_mem _ fun l _ => neg_mem (Oh_mul (hmO' i l) (ho l j)), ?_⟩
    have hPQ : finMat σ J g⁻¹ * finMat σ J g = 1 := by rw [← finMat_mul, inv_mul_cancel, finMat_one]
    have e1 : finMat σ J (g⁻¹ * emb σ J γ) - 1 =
        finMat σ J g⁻¹ * (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (Af F)) - finMat σ J g) := by
      rw [finMat_mul, finMat_emb, Matrix.mul_sub, hPQ]
    rw [e1, Matrix.mul_apply, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hl := hoe l j
    simp only [Matrix.sub_apply, Matrix.map_apply] at hl ⊢
    have e2 : ε * (finMat σ J g⁻¹ i l * (inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j) - finMat σ J g l j)) =
        -(finMat σ J g⁻¹ i l * (ε * (finMat σ J g l j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) l j)))) := by
      ring
    rw [e2, hl, hN0]
    simp only [nsmul_eq_mul, smul_neg]
    push_cast
    ring
  have small2 := invSmall σ J hJdet hdIi hdJi (evT T) ((emb σ J γ)⁻¹ * g) N1 (by
    rw [mul_inv_rev, inv_inv]; exact small1)
  have hεI : evT T ∈ intAf F := evT_int T
  have condA : ∀ y ∈ latHat F E L, ε • (finMat σ J (g⁻¹ * emb σ J γ)).mulVec y ∈ latHat F E L :=
    fun y hy => stabT L hu' hk' hεI _ (fun i j => by
      obtain ⟨o, ho, hoe⟩ := small1 i j
      exact ⟨(dI * dJ) • o, AddSubgroup.nsmul_mem _ ho _, by rw [hoe, smul_smul]; congr 1; rw [hN1]; ring⟩) hy
  have condB : ∀ y ∈ latHat F E L, ε • (finMat σ J ((emb σ J γ)⁻¹ * g)).mulVec y ∈ latHat F E L :=
    fun y hy => stabT L hu' hk' hεI _ small2 hy

  have hgen : ∀ m : ℕ, ¬ p ∣ m → ((m : 𝓞 E)) ∈ hcompl (K := E) P := fun m hm =>
    Submonoid.subset_closure ⟨hpm m hm, fun t ht => by
      have : t = (m : 𝓞 E) := by
        apply RingOfIntegers.coe_injective
        have ht' : algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (m : 𝓞 E) := by
          rw [ht, map_natCast, star_natCast]
        simpa using ht'
      rw [this]; exact hpm m hm⟩
  refine ⟨⟨emb σ J γ, emb_mem σ J γ⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨m2, hm2, hmx⟩ := locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT g (emb σ J γ)
      condB hsx
    refine ⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩
    rw [map_mul, map_natCast, mul_comm, mul_smul]
    exact hmx
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨m2, hm2, hmx⟩ := locCmpT σ J L hk hk' T p hpr.ne_zero hpr.one_lt.ne' hpT (emb σ J γ) g
      (fun y hy => by simpa using condA y hy) hsx
    refine ⟨s * (m2 : 𝓞 E), Submonoid.mul_mem _ hs (hgen m2 hm2), ?_⟩
    rw [map_mul, map_natCast, mul_comm, mul_smul]
    exact hmx

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LatticesCloseLocally
section
open NumberField PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Lin

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {M : ℕ}

theorem linOf_mul (b : Module.Basis (Fin M) E V) (u w : GL (Fin M) E) :
    linOf b (u * w) = linOf b u * linOf b w := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, LinearEquiv.mul_apply, equivFun_linOf, equivFun_linOf, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem linOf_one (b : Module.Basis (Fin M) E V) : linOf b (1 : GL (Fin M) E) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, Units.val_one, Matrix.one_mulVec]
  rfl

end Lin

theorem gmap_one {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (X : Submodule (𝓞 E) V) : gmap (1 : V ≃ₗ[E] V) X = X := by
  ext v
  simp [gmap, Submodule.mem_map]

theorem lattices_close_locally : LatClose := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  classical
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL0
  obtain ⟨u, hu, hu'⟩ := up_nat (crdOf b L0) ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat (crdOf b L0) ⟨c2, hc2, hlow⟩
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹
  obtain ⟨dg, hdg, hdgi⟩ := mat_den ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
  set Nn : ℕ := dg * dI * dJ * (u * k) with hNn
  have hNpos : 0 < Nn := by positivity
  refine ⟨(Nn : 𝓞 F), by exact_mod_cast hNpos.ne', fun D' hD' γ hγ S hS hcong => ?_⟩
  obtain ⟨c, rfl⟩ := hD'
  choose r hr y hy using hcong
  set R : 𝓞 E := ∏ q : Fin M × Fin M, r q.1 q.2 with hRd
  have hRS : R ∈ S := Submonoid.prod_mem _ fun q _ => hr q.1 q.2
  set cE : E := algebraMap F E ((c : 𝓞 F) : F) with hcE
  have hcEi : IsIntegral ℤ cE := c.isIntegral_coe.algebraMap
  have hz : ∀ i j, ∃ z : E, IsIntegral ℤ z ∧
      (R : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) = (Nn : E) * cE * z := by
    intro i j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun q : Fin M × Fin M => r q.1 q.2) (Finset.mem_univ (i, j))
    refine ⟨(q : E) * (y i j : E), q.isIntegral_coe.mul (y i j).isIntegral_coe, ?_⟩
    have e1 : (R : E) = (r i j : E) * (q : E) := by rw [hRd, hq]; push_cast; rfl
    rw [e1, mul_comm (r i j : E) (q : E), mul_assoc, hy i j]
    have e2 : algebraMap F E (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : E) * cE := by
      have e5 : (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : F) * ((c : 𝓞 F) : F) := by push_cast; ring
      rw [e5, map_mul, map_natCast]
    rw [e2]; ring
  choose z hzi hze using hz
  set gi : Matrix (Fin M) (Fin M) E := ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hgi
  set K : GL (Fin M) E := g⁻¹ * γ with hKd
  set Km : Matrix (Fin M) (Fin M) E := (K : Matrix (Fin M) (Fin M) E) with hKm
  have hgig : gi * (g : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  set e0 : Fin M → Fin M → E := fun i j => -cE * ∑ l, ((dg : E) * gi i l) * z l j with he0d
  have he0i : ∀ i j, IsIntegral ℤ (e0 i j) := fun i j =>
    (hcEi.neg).mul (IsIntegral.sum _ fun l _ => (hdgi i l).mul (hzi l j))
  have hK1 : ∀ i j, (algebraMap (𝓞 E) E R) * (Km - 1) i j = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * e0 i j) := by
    intro i j
    have eK : Km - 1 = gi * ((γ : Matrix (Fin M) (Fin M) E) - (g : Matrix (Fin M) (Fin M) E)) := by
      rw [hKm, hKd, Units.val_mul, Matrix.mul_sub, hgig]
    rw [eK, Matrix.mul_apply, Finset.mul_sum, he0d]
    simp only [Matrix.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hze l j
    change (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) = _
    have e3 : (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) =
        -(gi i l * ((R : E) * ((g : Matrix (Fin M) (Fin M) E) l j - (γ : Matrix (Fin M) (Fin M) E) l j))) := by ring
    rw [e3, this, hNn]
    push_cast
    ring

  have hKu : K ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J := (PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).mul_mem ((PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).inv_mem hg) hγ
  have hKu' : PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km = J := hKu
  have hJJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  set KImage : Matrix (Fin M) (Fin M) E := ((K⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hKim
  have hKK : Km * KImage = 1 := by rw [hKm, hKim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKinv : KImage = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by
    calc KImage = J⁻¹ * J * KImage := by rw [hJJ, Matrix.one_mul]
      _ = J⁻¹ * (PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km) * KImage := by rw [hKu']
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * (Km * KImage) := by simp only [Matrix.mul_assoc]
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by rw [hKK, Matrix.mul_one]
  have hcs : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) = PI.UnitaryApproxDefs.cT (σ : E →+* E) Km - 1 := by
    have h1 := PI.UnitaryApproxDefs.cT_one (n := Fin M) (σ : E →+* E)
    unfold PI.UnitaryApproxDefs.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hKi1 : KImage - 1 = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) * J := by
    rw [hKinv, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]
  have hR0 : σ (algebraMap (𝓞 E) E R) = algebraMap (𝓞 E) E R := hS R hRS
  have hK2 : ∀ i j, (algebraMap (𝓞 E) E R) * (KImage - 1) i j = ((u * k : ℕ) : E) *
      (∑ a, ∑ b', ((dI : E) * J⁻¹ i a) * σ (e0 b' a) * ((dJ : E) * J b' j)) := by
    intro i j
    rw [hKi1]
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ => ?_
    have hσK : (algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a) = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * σ (e0 b' a)) := by
      rw [← hR0, ← map_mul, hK1 b' a, map_mul, map_mul, map_natCast, map_natCast]
    have hX : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) a b' = σ ((Km - 1) b' a) := rfl
    rw [hX]
    calc (algebraMap (𝓞 E) E R) * (J⁻¹ i a * σ ((Km - 1) b' a) * J b' j)
        = J⁻¹ i a * ((algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a)) * J b' j := by ring
      _ = _ := by rw [hσK]; push_cast; ring

  have h1 : gmap (linOf b K) L0 ≤ locS S L0 := gmap_le_locS b L0 S K fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' Km R _ (fun i j => (isIntegral_natCast _).mul (he0i i j)) hK1 hx⟩
  have h2 : gmap (linOf b K⁻¹) L0 ≤ locS S L0 := gmap_le_locS b L0 S K⁻¹ fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' KImage R _ (fun i j => IsIntegral.sum _ fun a _ =>
      IsIntegral.sum _ fun b' _ => ((hdIi i a).mul (int_sigma (σ : E →+* E) (he0i b' a))).mul (hdJi b' j)) hK2 hx⟩
  have h3 : L0 ≤ locS S (gmap (linOf b K) L0) := by
    have e4 : gmap (linOf b K) (gmap (linOf b K⁻¹) L0) = L0 := by
      rw [← gmap_comp, ← linOf_mul, mul_inv_cancel, linOf_one, gmap_one]
    calc L0 = gmap (linOf b K) (gmap (linOf b K⁻¹) L0) := e4.symm
      _ ≤ gmap (linOf b K) (locS S L0) := Submodule.map_mono h2
      _ = locS S (gmap (linOf b K) L0) := gmap_locS _ S L0
  have hKeq : locS S (gmap (linOf b K) L0) = locS S L0 := locS_eq_of S h1 h3
  have hγK : γ = g * K := by rw [hKd, mul_inv_cancel_left]
  rw [hγK, linOf_mul, gmap_comp, ← gmap_locS, hKeq, gmap_locS]

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermT
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def LocInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) (z : F) (c : 𝓞 F)
    (u : t.adicCompletion F), u ∈ t.adicCompletionIntegers F →
    algebraMap F (t.adicCompletion F) z = algebraMap F (t.adicCompletion F) (c : F) * u →
    ∃ d ∈ t.asIdeal.primeCompl, ∃ a : 𝓞 F, z * (d : F) = (c : F) * (a : F)

def tcoord {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →ₗ[F] R :=
  (TensorProduct.lid F R).toLinearMap ∘ₗ TensorProduct.map (B.coord k) LinearMap.id

theorem tcoord_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] (x : E) (y : R) :
    tcoord B k R (x ⊗ₜ[F] y) = B.coord k x • y := by
  simp [tcoord]

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

