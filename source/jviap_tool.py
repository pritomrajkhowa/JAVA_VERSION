#!/usr/bin/python

import sys
import jviap


if sys.argv[1:] == ['-version']:
	print jviap.getVersion()
elif sys.argv[1:] == ['--version']:
	print jviap.getVersion()
elif sys.argv[1:] != [] and sys.argv[-1] is not None:
	filename=sys.argv[-1]	
	if len(sys.argv[1:])==1: 
		jviap.translate_Java(filename)
	elif len(sys.argv[1:])==2: 
		propertyfile=sys.argv[-2]
		if '.prp' in propertyfile:
			jviap.translate_Java(filename,propertyfile)
		else:
			jviap.translate_Java(file_name)	
	else:
		jviap.translate_Java(file_name)

