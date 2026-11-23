module

public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0004
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0003
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

def geoExample (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := Empty
  dim := fun Y => Empty.elim Y
  Fn := fun Y => Empty.elim Y
  fnField := fun Y => Empty.elim Y
  fnAlg := fun Y => Empty.elim Y
  Dv := fun Y => Empty.elim Y
  dvGrp := fun Y => Empty.elim Y
  Eff := fun Y => Empty.elim Y
  eff_zero := fun Y => Empty.elim Y
  eff_add := fun Y => Empty.elim Y
  H0 := fun Y => Empty.elim Y
  degreeZeroCohomology_finiteDimensional := fun Y => Empty.elim Y
  mul_mem_riemannRochSpace_add := fun Y => Empty.elim Y
  riemannRoch_mono := fun Y => Empty.elim Y
  KY := fun Y => Empty.elim Y
  Cl := fun Y => Empty.elim Y
  properCl := fun Y => Empty.elim Y
  subCl := fun Y => Empty.elim Y
  supp := fun Y => Empty.elim Y
  inter := fun Y => Empty.elim Y
  nef := fun Y => Empty.elim Y
  big := fun Y => Empty.elim Y
  bpf := fun Y => Empty.elim Y
  phiBir := fun Y => Empty.elim Y
  phiNoContr := fun Y => Empty.elim Y
  vanishOn := fun Y => Empty.elim Y
  hdim := fun Y => Empty.elim Y
  pts := fun Y => Empty.elim Y
  ptsMeas := fun Y => Empty.elim Y
  vol := fun Y => Empty.elim Y
  FnC := fun Y => Empty.elim Y
  fnCRing := fun Y => Empty.elim Y
  fnCAlg := fun Y => Empty.elim Y
  cx := fun Y => Empty.elim Y
  cx_smul := fun Y => Empty.elim Y
  Met := fun Y => Empty.elim Y
  mAdd := fun Y => Empty.elim Y
  mPow := fun Y => Empty.elim Y
  fsMet := fun Y => Empty.elim Y
  pn := fun Y => Empty.elim Y
  pnK := fun Y => Empty.elim Y
  mSmooth := fun Y => Empty.elim Y
  mPsh := fun Y => Empty.elim Y
  redZero := fun Y => Empty.elim Y
  agreeOn := fun Y => Empty.elim Y
  resNorm := fun Y => Empty.elim Y
  Adl := fun Y => Empty.elim Y
  ofW := fun Y => Empty.elim Y
  twist := fun Y => Empty.elim Y
  arTop := fun Y => Empty.elim Y
  arVol := fun Y => Empty.elim Y
  nefA := fun Y => Empty.elim Y
  supInf := fun Y => Empty.elim Y
  supFin := fun Y => Empty.elim Y
  cutGood := fun Y => Empty.elim Y
  cutHt := fun Y => Empty.elim Y
  cutOrd := fun Y => Empty.elim Y
  resFull := fun Y => Empty.elim Y
  resDeg := fun Y => Empty.elim Y
  supInf_ofW := fun Y => Empty.elim Y
  supInf_twist := fun Y => Empty.elim Y
  supFin_twist := fun Y => Empty.elim Y
  regOn := fun Y => Empty.elim Y

variable (D : D7)

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.GenericMemberLevelNearLower
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.Inhab
open scoped TensorProduct

section SpacesG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

variable (s : ℕ) (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

end SpacesG

section RowsG

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

abbrev rowsG : Rows.Data R where
  LL := LL
  embLL := embLL
  places := P
  O := 𝓞 LL
  OtoLL := algebraMap (𝓞 LL) LL
  Tau := Tau
  card_Tau := hTau
  Tup := Unit
  mu0 := ()
  muStar := ()
  muStar' := ()
  muAt := fun _ => ()
  muAt_conj := fun _ => rfl
  muTw := fun _ => ()
  muTw_conj := fun _ => rfl
  muAt_or := fun _ => Or.inl rfl
  EE := Z0
  Drows := 0
  onb := EuclideanSpace.basisFun (Fin 0) ℂ
  Dall := 0
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Z0
  D0 := 0
  onb0 := EuclideanSpace.basisFun (Fin 0) ℂ
  FT := Empty
  ft := fun i => i.elim0
  ft0 := fun i => i.elim0
  Dstar := Dst
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => LinearIsometryEquiv.refl ℂ Z0
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => zeroOLat _
  eOp := fun _ => 0
  eOp_idem := fun _ => by simp
  eOp_sa := fun _ => LinearMap.IsSymmetric.zero
  restRowsFiniteGroupCard := cg
  restRowsFiniteGroupCard_pos := hcg
  Word := Unit
  Mu := fun _ => Z0
  perCol := fun _ _ _ _ => 0
  Bu := fun _ _ _ => 0
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  Mj := fun _ => Z0
  MjLat := fun _ => zeroOLat _
  kaBig := fun _ _ _ => 0
  kaSmall := fun _ _ _ => 0
  Mt := fun _ _ => Z0
  MtLat := fun _ _ => zeroOLat _
  MtL := fun _ _ => PUnit
  jMt := fun _ _ => 0
  jMt_basis := by
    intro μ j b
    have : IsEmpty (Module.Free.ChooseBasisIndex LL PUnit) :=
      ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
    exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩
  MtLat_sub := fun _ _ x hx => by simp [zeroOLat] at hx
  eMt := fun _ _ => 0
  eMt_idem := fun _ _ => by simp
  eMt_sa := fun _ _ => LinearMap.IsSymmetric.zero
  eMt_LL := fun _ _ _ => ⟨0, by simp⟩
  thetaP := fun _ _ => 0
  isot := fun _ i => i.elim
  lamP := fun _ _ _ => 0
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0
  etaJ := fun _ _ => 0
  etaJ_nonneg := fun _ _ => le_refl _
  shaLen := sha
  shaLen_nonneg := hsha

end RowsG

theorem N_even (R : Ranks) (j : ℕ) : ∃ a : ℕ, R.N j = 2 * a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  exact ⟨a + j * (b + 1), by unfold Ranks.N; rw [ha, hb]; ring⟩

theorem sInt (R : Ranks) (hc : HCParam R) (i : Fin R.m) :
    (∃ a : ℤ, sExp R (hc.e i) (i.1 + 1) = a) ∧ (∃ a : ℤ, sExp' R (hc.e i) (i.1 + 1) = a) := by
  obtain ⟨z, hz⟩ := hc.e_int i
  obtain ⟨a, ha⟩ := N_even R i.1
  obtain ⟨b, hb⟩ := N_even R (i.1 + 1)
  refine ⟨⟨z - a, ?_⟩, ⟨z - b, ?_⟩⟩
  · unfold sExp; rw [Nat.add_sub_cancel, ha, hz]; push_cast; ring
  · unfold sExp'; rw [hb, hz]; push_cast; ring

section MemberG

variable {R : Ranks} (hc : HCParam R) (Tau : Type) [Fintype Tau]

variable (T : ℕ) [hT : Fact T.Prime]

end MemberG

section Record

variable {s : ℕ}

variable (H : Host (Rt s))

variable (hc : HCParam (Rt s))
  (hgap : ∀ (l : ℕ) (h : l + 1 < (Rt s).k - 1), hc.v ⟨l, by omega⟩ - hc.v ⟨l + 1, h⟩ = 4 * 1)
  (hlet : ∀ (l : ℕ) (h : l < (Rt s).k - 2), hc.u ⟨l + 1, by omega⟩ = hc.v ⟨l, by omega⟩ - 1 / 2)

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / 64) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)


end Record

end Formalism.BasicNotions.Examples₂
end
end

