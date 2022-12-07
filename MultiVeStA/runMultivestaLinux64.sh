#Brake model
#java -jar multivesta.jar client -sd vesta.pmaude.NewAPMaudeState -m brake-system.maude -o '-mc ./Maude-3.0+yices2-linux/maude-Yices2.linux64' -f ./multiquatex/brakeSystem.multiquatex -l 1 -osws ONESTEP -bs 28 -vp true -verboseServers false -a 0.05 -d1 0.1 -ir 1

#Gear model
java -jar multivesta.jar client -sd vesta.pmaude.NewAPMaudeState -m gear-system.maude -o '-mc ./Maude-3.0+yices2-linux/maude-Yices2.linux64' -f ./multiquatex/gearSystem.multiquatex -l 1 -osws ONESTEP -bs 28 -vp true -verboseServers false -a 0.05 -d1 0.01 -ir 1

#P2P protocol
#java -jar multivesta.jar client -sd vesta.pmaude.NewAPMaudeState -m p2p-protocol.maude -o '-mc ./Maude-3.0+yices2-linux/maude-Yices2.linux64' -f ./multiquatex/p2pProtocol.multiquatex -l 1 -osws ONESTEP -bs 28 -vp true -verboseServers false -a 0.05 -d1 5 -ir 1

#B-retrans-4
#java -jar multivesta.jar client -sd vesta.pmaude.NewAPMaudeState -m b-retrans-4.maude -o '-mc ./Maude-3.0+yices2-linux/maude-Yices2.linux64' -f ./multiquatex/bRetrans4.multiquatex -l 1 -osws ONESTEP -bs 28 -vp true -verboseServers false -a 0.05 -d1 0.1 -ir 1

#B-retrans-5
#java -jar multivesta.jar client -sd vesta.pmaude.NewAPMaudeState -m b-retrans-5.maude -o '-mc ./Maude-3.0+yices2-linux/maude-Yices2.linux64' -f ./multiquatex/bRetrans5.multiquatex -l 1 -osws ONESTEP -bs 28 -vp true -verboseServers false -a 0.05 -d1 0.1 -ir 1
