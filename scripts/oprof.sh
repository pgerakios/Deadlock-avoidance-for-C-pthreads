#! /bin/sh
bash file=$1

sudo opcontrol --reset
sudo opcontrol --start
./$@ > /dev/null
sudo opcontrol --shutdown
opreport -lt1
