
modeleData = [{'SigInA': 0x00000001, 'SigInB': 0, 'SigModeleOut': 0x00001101},
                                 {'SigInA': 0x00000000, 'SigInB': 0, 'SigModeleOut': 0x11000111}, 
                                 {'SigInA': 0x00000000, 'SigInB': 0, 'SigModeleOut': 0x11011100},
                                 {'SigInA': 0x00000000, 'SigInB': 0, 'SigModeleOut': 0x11001100},
                                 {'SigInA': 0x00001001, 'SigInB': 0, 'SigModeleOut': 0x01110001},
                                 {'SigInA': 0x00000000, 'SigInB': 0, 'SigModeleOut': 0x10110001},
                                 {'SigInA': 0x10011111, 'SigInB': 1, 'SigModeleOut': 0x10011111}]
les_6_premier_sigInA = []

               

for x in modeleData:
    les_6_premier_sigInA.append(x["SigInA"])
    if len(les_6_premier_sigInA) == 6:
        break
    

print(les_6_premier_sigInA)