import float.basic 
import float.div

set_option profiler true

-- Test 1: 0 + 1
#eval rat.mk 0 1 + rat.mk 1 1 
#eval float.mk 0 0 + float.mk 1 0 -- OK

-- Test 2: 1/1024 + 3/4096
#eval rat.mk 1 1024 + rat.mk 3 4096 
#eval float.mk 1 (-10) + float.mk 3 (-12) -- OK

-- Test 3: 12345/1048576 + -6789/32768
#eval rat.mk 12345 1048576 + rat.mk (-6789) 32768 
#eval float.mk 12345 (-20) + float.mk (-6789) (-15) 

-- Test 4: 0 + 1
#eval rat.mk 0 1 * rat.mk 1 1 
#eval float.mk 0 0 * float.mk 1 0 -- OK

-- Test 5: 1/1024 * 3/4096
#eval rat.mk 1 1024 * rat.mk 3 4096 
#eval float.eval (float.mk 1 (-10) * float.mk 3 (-12)) -- OK

-- Test 6: 12345/1048576 * -6789/32768
#eval rat.mk 12345 1048576 * rat.mk (-6789) 32768 
#eval ((12345 * 6789) * 2 ^ ((-20) + (-15) : ℤ) : ℚ)
example : float.mk 12345 (-20) * float.mk (-6789) (-15) = float.mk (-83810205) (-35) :=
by { simp only [float.mul_def], apply congr_arg2; norm_num, }
#eval rat.mk (-83810205) 34359738368
#eval rat.mk (-99838) 8
#eval ((-99838) * 2 ^ (-3 : ℤ) : ℚ) 
#eval float.mk (-99838) (-3)
#eval float.mk 12345 (-20) * float.mk (-6789) (-15) 
