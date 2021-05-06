import float.basic 
import float.round
import float.div

set_option profiler true

-- Test 1: 0 + 1
#eval rat.mk 0 1 + rat.mk 1 1 
#eval float.mk 0 0 + float.mk 1 0 -- OK

-- Test 2: 1/1024 + 3/4096
#eval rat.mk 1 1024 + rat.mk 3 4096 
#eval float.mk 1 (-10) + float.mk 3 (-12)

-- Test 3: 12345/1048576 + -6789/32768
#eval rat.mk 12345 1048576 + rat.mk (-6789) 32768 
#eval float.mk 12345 (-20) + float.mk (-6789) (-15) 

-- Test 4: 0 + 1
#eval rat.mk 0 1 * rat.mk 1 1 
#eval float.mk 0 0 * float.mk 1 0 

-- Test 5: 1/1024 * 3/4096
#eval rat.mk 1 1024 * rat.mk 3 4096 
#eval float.mk 1 (-10) * float.mk 3 (-12)

-- Test 6: 12345/1048576 * -6789/32768
#eval rat.mk 12345 1048576 * rat.mk (-6789) 32768 
#eval float.mk 12345 (-20) * float.mk (-6789) (-15) 

-- Test 4: 0 + 1
#eval rat.mk 0 1 / rat.mk 1 1 
#eval float.mk 0 0 / float.mk 1 0 

-- Test 5: 1/1024 * 3/4096
#eval rat.mk 1 1024 / rat.mk 3 4096 
#eval float.mk 1 (-10) / float.mk 3 (-12)

-- Test 6: 12345/1048576 * -6789/32768
#eval rat.mk 12345 1048576 / rat.mk (-6789) 32768 
#eval float.mk 12345 (-20) / float.mk (-6789) (-15) 

#eval rat.mk 12345789101112 (2 ^ 100) / rat.mk (-12345789101112) (2 ^ 7898) 
#eval round_up 10 (rat.mk 12345789101112 (2 ^ 100) / rat.mk (-12345789101112) (2 ^ 7898))
--#eval float.mk 12345789101112 (-20) / float.mk (-12345789101112) (-15) 
#eval rat.mk 12345789101112 (2 ^ 100) + rat.mk (-12345789101112) (2 ^ 7898) 
#eval float.mk 12345789101112 (-100) + float.mk (-12345789101112) (-7898) 

-- Still not quick enough, rounding directly float_raw?
