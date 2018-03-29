s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T30-[4,4,2]-44-422-22211-g0";
s`BelyiDBFilename := "8T30-[4,4,2]-44-422-22211-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 5, 8, 3, 6, 1, 4, 7, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 5, 8, 3, 6, 1, 4, 7, 2 ]:
 Order := 64 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 5, 8, 3, 6, 1, 4, 7, 2 ]:
 Order := 64 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 5, 8, 3, 6, 1, 4, 7, 2 ]:
 Order := 64 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 5, 8, 3, 6, 1, 4, 7, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 3, 2, 5, 8, 7, 6, 1 ],
\[ 5, 8, 3, 6, 1, 4, 7, 2 ]:
 Order := 64 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 8, 7, 6, 1, 4, 3, 2, 5 ],
[ 1, 4, 7, 2, 5, 8, 3, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 >) |
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 3, 2, 5, 8, 7, 6, 1 ],
[ 5, 8, 3, 6, 1, 4, 7, 2 ]
],
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 3, 2, 1, 8, 7, 6, 5, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 8, 7, 6, 1, 4, 3, 2, 5 ],
[ 1, 4, 7, 2, 5, 8, 3, 6 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
