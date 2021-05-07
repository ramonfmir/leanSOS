import float.basic 
import float.round
import float.div

set_option profiler true

-- Test add 1: 0 + 1
#eval rat.mk 0 1 + rat.mk 1 1 
#eval float.mk 0 0 + float.mk 1 0 -- OK

-- Test add 2: 1/1024 + 3/4096
#eval rat.mk 1 1024 + rat.mk 3 4096 
#eval float.mk 1 (-10) + float.mk 3 (-12)

-- Test add 3: 12345/1048576 + -6789/32768
#eval rat.mk 12345 1048576 + rat.mk (-6789) 32768 
#eval float.mk 12345 (-20) + float.mk (-6789) (-15) 

-- Test add 4: 12345789101112/2^100 + -123457891011/2^7898
#eval rat.mk 12345789101112 (2 ^ 100) + rat.mk (-123457891011) (2 ^ 7898) 
#eval float.mk 12345789101112 (-100) + float.mk (-1234578910111) (-7898) 

-- Test mul 1: 0 * 1
#eval rat.mk 0 1 * rat.mk 1 1 
#eval float.mk 0 0 * float.mk 1 0 

-- Test mul 2: 1/1024 * 3/4096
#eval rat.mk 1 1024 * rat.mk 3 4096 
#eval float.mk 1 (-10) * float.mk 3 (-12)

-- Test mul 3: 12345/1048576 * -6789/32768
#eval rat.mk 12345 1048576 * rat.mk (-6789) 32768 
#eval float.mk 12345 (-20) * float.mk (-6789) (-15) 

-- Test mul 4: 12345789101112/2^100 * -123457891011/2^7898
#eval rat.mk 12345789101112 (2 ^ 100) * rat.mk (-123457891011) (2 ^ 7898) 
#eval float.mk 12345789101112 (-100) * float.mk (-1234578910111) (-7898) 

-- Test div 1: 0 / 1
#eval rat.mk 0 1 / rat.mk 1 1 
#eval float.mk 0 0 / float.mk 1 0 

-- Test div 2: 1/1024 / 3/4096
#eval rat.mk 1 1024 / rat.mk 3 4096 
#eval float.mk 1 (-10) / float.mk 3 (-12)

-- Test div 3: 12345/1048576 / -6789/32768
#eval rat.mk 12345 1048576 / rat.mk (-6789) 32768 
#eval float.mk 12345 (-20) / float.mk (-6789) (-15) 

-- Test div 4: 12345789101112/2^100 / -123457891011/2^7898
#eval rat.mk 12345789101112 (2 ^ 100) / rat.mk (-123457891011) (2 ^ 7898) 
#eval float.mk 12345789101112 (-100) / float.mk (-1234578910111) (-7898) 
